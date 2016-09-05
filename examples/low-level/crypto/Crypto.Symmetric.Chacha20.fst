module Crypto.Symmetric.Chacha20

open FStar.Mul
open FStar.Ghost
(*  Machine integers *)
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
(*  Effects and memory layout *)
open FStar.HyperStack
open FStar.HST
(*  Buffers *)
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

(* ************************************* *)
(*             Chacha 20 code            *)
(* ************************************* *)

type key = k:bytes{length k = 32} 

// why not treating the IV and Constant as bytes too? 

// should be abstract, but not compatible with caller allocation.
//abstract type matrix = m:uint32s{length m = 16}
type matrix = m:uint32s{length m = 16}

//effect UPD (m:matrix) = STL unit 
//  (requires (fun h -> live h m)) 
//  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
// not usable?

type shuffle = 
  m:matrix -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))

private val quarter_round:
  m:matrix -> 
  a:u32{v a < 16} -> 
  b:u32{v b < 16} -> 
  c:u32{v c < 16} -> 
  d:u32{v d < 16} -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let quarter_round m a b c d = 
  let line a b d s = 
    upd m a (m.(a) +%^ m.(b));
    upd m d((m.(d) ^^  m.(a)) <<< s) in
  line a b d 16ul;
  line c d b 12ul;
  line a b d  8ul; 
  line c d b  7ul
// check this is fully inlined

(*
  upd m a (m.(a) +%^ m.(b));
  upd m d((m.(d) ^^  m.(a)) <<< 16ul); 
  upd m c (m.(c) +%^ m.(d)); 
  upd m b((m.(b) ^^  m.(c)) <<< 12ul);
  upd m a (m.(a) +%^ m.(b)); 
  upd m d((m.(d) ^^  m.(a)) <<<  8ul);
  upd m c (m.(c) +%^ m.(d)); 
  upd m b((m.(b) ^^  m.(c)) <<<  7ul)
*)
    
private val column_round: shuffle 
let column_round m =
  quarter_round m 0ul 4ul  8ul 12ul;
  quarter_round m 1ul 5ul  9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

private val diagonal_round: shuffle
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul  8ul 13ul;
  quarter_round m 3ul 4ul  9ul 14ul

private val rounds: shuffle 
let rounds m = (* 20 rounds *)
  column_round m; diagonal_round m; 
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m

val chacha20_init: 
  m:matrix -> k:key{disjoint m k} -> counter:u32 -> iv:UInt64.t -> constant:UInt32.t -> 
  STL unit
  (requires (fun h -> live h m /\ live h k))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))

private val updkey:
  m:matrix -> k:key{disjoint m k} -> i:u32 { 4 <= v i /\ v i < 12 } -> 
  STL unit
  (requires (fun h -> live h m /\ live h k))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let updkey m k i =
  upd m i (uint32_of_bytes (sub k ((i -^ 4ul) *^ 4ul) 4ul))
  //upd m (i +^ 4ul) (uint32_of_bytes (sub k (i *^ 4ul) 4ul))

let chacha20_init m k counter iv constant =
  upd m  0ul 0x61707865ul;
  upd m  1ul 0x3320646eul;
  upd m  2ul 0x79622d32ul;
  upd m  3ul 0x6b206574ul;
  updkey m k  4ul;
  updkey m k  5ul;
  updkey m k  6ul;
  updkey m k  7ul;
  updkey m k  8ul;
  updkey m k  9ul;
  updkey m k 10ul;
  updkey m k 11ul;
  upd m 12ul counter; 
  upd m 13ul constant;
  upd m 14ul (Int.Cast.uint64_to_uint32 iv);
  upd m 15ul (Int.Cast.uint64_to_uint32 (UInt64.shift_right iv 32ul))

private val sum_matrixes: new_state:matrix -> 
  old_state:matrix{disjoint new_state old_state} -> 
  STL unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))

let sum_matrixes m m0 =
  let add i = upd m i (m.(i) +%^ m0.(i)) in // inlined? 
  add  0ul;
  add  1ul;
  add  2ul;
  add  3ul;
  add  4ul;
  add  5ul;
  add  6ul;
  add  7ul;
  add  8ul;
  add  9ul;
  add 10ul;
  add 11ul;
  add 12ul;
  add 13ul;
  add 14ul;
  add 15ul

val chacha20_update: 
  output:bytes -> 
  state:uint32s{length state = 32 /\ disjoint state output} ->
  len:u32{v len <= 64 /\ length output >= v len} -> STL unit
    (requires (fun h -> live h state /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_update output state len =
  (* Initial state *) 
  let m  = sub state  0ul 16ul in
  let m0 = sub state 16ul 16ul in // do we ever rely on m and m0 being contiguous?
  blit m 0ul m0 0ul 16ul;
  rounds m;
  (* Sum the matrixes *)
  sum_matrixes m m0;
  (* Serialize the state into byte stream *)
  bytes_of_uint32s output m len
// avoid this copy when XORing? merge the sum_matrix and output loops? we don't use m0 afterward. 

// for each block, we always first call _init then _update; 
// it may be faster to re-use an expanded key (m0) updated in place,
// and avoid passing around (key, counter, iv, constant), or to replace
// blit/sum by a _add variant of _init.

(* Loop over the Chacha20_update function *)
private val chacha20_loop:
  state:uint32s{length state = 32} -> k:key{disjoint state k} -> 
  counter:u32 -> 
  iv:UInt64.t -> 
  constant:UInt32.t ->
  plaintext:bytes{disjoint state plaintext (* /\ disjoint k plaintext /\ disjoint nonce plaintext *)} -> 
  ciphertext:bytes{disjoint state ciphertext /\ disjoint k ciphertext /\ disjoint plaintext ciphertext} -> j:u32 -> max:u32{v j <= v max /\ v counter + v max < pow2 n} ->
  STL unit
    (requires (fun h -> live h state /\ live h k /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (v max-v j) * 64  /\ length ciphertext >= (v max-v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))

let rec chacha20_loop state key counter iv constant plaintext ciphertext j max =
  if j =^ max then () 
  else
    begin
      // fails to verify; timeout? simpler by avoiding /64 ? 
      assume false; 
      
      (* Generate new state for block *)
      cut(length ciphertext >= 64);
      let cipher_block = sub ciphertext 0ul 64ul in

      let ciphertext' = sub ciphertext 64ul (64ul *^ (max -^ j -^ 1ul)) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (64ul *^ (max -^ j -^ 1ul)) in
      chacha20_init (sub state 0ul 16ul) key (counter +^ j) iv constant;
      chacha20_update cipher_block state 64ul;
      (* XOR the key stream with the plaintext *)
      xor_bytes_inplace cipher_block plain_block 64ul;
      (* Apply Chacha20 to the next blocks *)
      chacha20_loop state key counter iv constant plaintext' ciphertext' (j +^ 1ul) max
    end

private val chacha20_encrypt_body: state:uint32s{length state = 32} -> 
  ciphertext:bytes{disjoint state ciphertext} -> 
  k:key{disjoint ciphertext k /\ disjoint k state} -> 
  counter:u32 -> iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint state plaintext} -> 
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h state /\ live h ciphertext /\ live h k /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1))

let chacha20_encrypt_body state ciphertext key counter iv constant plaintext len =
  assume false; 
  
  (* Compute the number of 'plain' blocks, the length is assumed to be a public value *)
  let max = (len /^ 64ul) in
  let rem = len %^ 64ul in
  (* apply max blocks of Chacha20 *)
  chacha20_loop state key counter iv constant plaintext ciphertext 0ul max;
  (* If complete, return *)
  if rem =^ 0ul 
  then ()
  else (* compute final, partial block *)
    begin
      let cipher_block = sub ciphertext (UInt32.mul 64ul max) rem in 
      let plain_block = sub plaintext (UInt32.mul 64ul max) rem in 
      chacha20_init state key (counter +^ max) iv constant;
      chacha20_update cipher_block state rem;
      xor_bytes_inplace cipher_block plain_block rem
    end

val chacha20_encrypt: 
  ciphertext:bytes -> k:key{disjoint ciphertext k} -> counter:u32 -> 
  iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint k plaintext} ->
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h ciphertext /\ live h k /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let chacha20_encrypt ciphertext key counter iv constant plaintext len =
  push_frame ();
  let state = create 0ul 32ul in
  (* Apply Chacha20 on plaintext and store the result in the 'ciphertext' buffer *)
  chacha20_encrypt_body state ciphertext key counter iv constant plaintext len;
  pop_frame ()
