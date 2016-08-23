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
val quarter_round: m:uint32s{length m = 16} -> 
  a:u32{v a < 16} -> b:u32{v b<16} -> c:u32{v c<16} -> d:u32{v d<16} -> STL unit 
  (requires (fun h -> live h m)) 
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  upd m a (index m a +%^ index m b);
  upd m d (index m d ^^ index m a);
  let (tmp:u32) = index m d in 
  upd m d (tmp <<< UInt32.uint_to_t 16); 
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 12);
  upd m a (index m a +%^ index m b); 
  upd m d (index m d ^^ index m a); 
  let tmp = index m d in
  upd m d (tmp <<< UInt32.uint_to_t 8);
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 7)

val column_round: m:uint32s{length m = 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let column_round m =
  quarter_round m 0ul 4ul 8ul 12ul;
  quarter_round m 1ul 5ul 9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

val diagonal_round: m:uint32s{length m = 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul 8ul 13ul;
  quarter_round m 3ul 4ul 9ul 14ul

val chacha20_init: state:uint32s{length state >= 16} -> 
  key:bytes{length key = 32 /\ disjoint state key} -> counter:u32 -> iv:UInt64.t -> 
  constant:UInt32.t -> STL unit
  (requires (fun h -> live h state /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let chacha20_init state key counter iv constant =
  (* Key part *)
  let k0 = sub key 0ul  4ul in 
  let k1 = sub key 4ul  4ul in 
  let k2 = sub key 8ul  4ul in 
  let k3 = sub key 12ul 4ul in 
  let k4 = sub key 16ul 4ul in 
  let k5 = sub key 20ul 4ul in 
  let k6 = sub key 24ul 4ul in 
  let k7 = sub key 28ul 4ul in
  let k0 =  (uint32_of_bytes k0) in
  let k1 =  (uint32_of_bytes k1) in 
  let k2 =  (uint32_of_bytes k2) in 
  let k3 =  (uint32_of_bytes k3) in 
  let k4 =  (uint32_of_bytes k4) in
  let k5 =  (uint32_of_bytes k5) in
  let k6 =  (uint32_of_bytes k6) in
  let k7 =  (uint32_of_bytes k7) in
  (* Nonce part *)
  let n0 = Int.Cast.uint64_to_uint32 iv in
  let n1 = Int.Cast.uint64_to_uint32 (UInt64.shift_right iv 32ul) in
  (* Constant part *)
  upd state 0ul 0x61707865ul;
  upd state 1ul 0x3320646eul;
  upd state 2ul 0x79622d32ul;
  upd state 3ul 0x6b206574ul;
  (* Update with key *)
  upd state 4ul  (k0);
  upd state 5ul  (k1); 
  upd state 6ul  (k2); 
  upd state 7ul  (k3); 
  upd state 8ul  (k4);
  upd state 9ul  (k5);
  upd state 10ul (k6);
  upd state 11ul (k7);
  (* Block counter part *)
  upd state 12ul counter; 
  (* Update with nonces *)
  upd state 13ul (constant);
  upd state 14ul (n0);
  upd state 15ul (n1)

val sum_matrixes: new_state:uint32s{length new_state >= 16} -> 
  old_state:uint32s{length old_state >= 16 /\ disjoint new_state old_state} -> STL unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  upd m 0ul (index m 0ul +%^ index m0 0ul); 
  upd m 1ul (index m 1ul +%^ index m0 1ul);
  upd m 2ul (index m 2ul +%^ index m0 2ul);
  upd m 3ul (index m 3ul +%^ index m0 3ul);
  upd m 4ul (index m 4ul +%^ index m0 4ul);
  upd m 5ul (index m 5ul +%^ index m0 5ul);
  upd m 6ul (index m 6ul +%^ index m0 6ul);
  upd m 7ul (index m 7ul +%^ index m0 7ul); 
  upd m 8ul (index m 8ul +%^ index m0 8ul);
  upd m 9ul (index m 9ul +%^ index m0 9ul); 
  upd m 10ul (index m 10ul +%^ index m0 10ul);
  upd m 11ul (index m 11ul +%^ index m0 11ul);
  upd m 12ul (index m 12ul +%^ index m0 12ul);
  upd m 13ul (index m 13ul +%^ index m0 13ul);
  upd m 14ul (index m 14ul +%^ index m0 14ul);
  upd m 15ul (index m 15ul +%^ index m0 15ul);
  ()

val chacha20_update: output:bytes -> state:uint32s{length state >= 32 /\ disjoint state output} ->
  len:u32{v len <= 64 /\ length output >= v len} -> STL unit
    (requires (fun h -> live h state /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_update output state len =
  (* Initial state *) 
  let m = sub state 0ul 16ul in
  let m0 = sub state 16ul 16ul in
  blit m 0ul m0 0ul 16ul;
  (* 20 rounds *)
  column_round m; diagonal_round m; 
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  (* Sum the matrixes *)
  sum_matrixes m m0;
  (* Serialize the state into byte stream *)
  bytes_of_uint32s output m len

(* Loop over the Chacha20_update function *)
val chacha20_loop:
  state:uint32s{length state >= 32} -> key:bytes{length key = 32 /\ disjoint state key} -> 
  counter:u32 -> 
  iv:UInt64.t -> 
  constant:UInt32.t ->
  plaintext:bytes{disjoint state plaintext (* /\ disjoint key plaintext /\ disjoint nonce plaintext *)} -> 
  ciphertext:bytes{disjoint state ciphertext /\ disjoint key ciphertext /\ disjoint plaintext ciphertext} -> j:u32 -> max:u32{v j <= v max /\ v counter + v max < pow2 n} ->
  STL unit
    (requires (fun h -> live h state /\ live h key /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (v max-v j) * 64  /\ length ciphertext >= (v max-v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))
let rec chacha20_loop state key counter iv constant plaintext ciphertext j max =
  if j =^ max then ()
  else 
    begin
      (* Generate new state for block *)
      let cipher_block = sub ciphertext 0ul 64ul in
      let ciphertext' = sub ciphertext 64ul (64ul *^ (max -^ j -^ 1ul)) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (64ul *^ (max -^ j -^ 1ul)) in
      chacha20_init state key (counter +^ j) iv constant;
      chacha20_update cipher_block state 64ul;
      (* XOR the key stream with the plaintext *)
      xor_bytes_inplace cipher_block plain_block 64ul;
      (* Apply Chacha20 to the next blocks *)
      chacha20_loop state key counter iv constant plaintext' ciphertext' (j +^ 1ul) max
    end

val chacha20_encrypt_body: state:uint32s{length state = 32} -> 
  ciphertext:bytes{disjoint state ciphertext} -> 
  key:bytes{length key = 32 /\ disjoint ciphertext key /\ disjoint key state} -> 
  counter:u32 -> iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint state plaintext} -> 
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h state /\ live h ciphertext /\ live h key /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1))
let chacha20_encrypt_body state ciphertext key counter iv constant plaintext len =
  (* Compute the number of 'plain' blocks, the length is assumed to be a public value *)
  let max = (len /^ 64ul) in
  let rem = len %^ 64ul in
  (* Apply Chacha20 max times *)
  chacha20_loop state key counter iv constant plaintext ciphertext 0ul max;
  (* If complete, return *)
  if rem =^ 0ul then ()
  (* Else compute one more block *)
  else
    begin
      let cipher_block = sub ciphertext (UInt32.mul 64ul max) rem in 
      let plain_block = sub plaintext (UInt32.mul 64ul max) rem in 
      chacha20_init state key (counter +^ max) iv constant;
      chacha20_update cipher_block state rem;
      xor_bytes_inplace cipher_block plain_block rem
    end

val chacha20_encrypt: 
  ciphertext:bytes -> key:bytes{length key = 32 /\ disjoint ciphertext key} -> counter:u32 -> 
  iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint key plaintext} ->
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let chacha20_encrypt ciphertext key counter iv constant plaintext len =
  push_frame ();
  let state = create 0ul 32ul in
  (* Apply Chacha20 on plaintext and store the result in the 'ciphertext' buffer *)
  chacha20_encrypt_body state ciphertext key counter iv constant plaintext len;
  pop_frame ()
