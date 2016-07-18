module Chacha20

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Int.Cast
open FStar.UInt8
open FStar.UInt32
open FStar.Buffer
open Low.Bytes

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let u32 = UInt32.t
let u8 = UInt8.t

(** Infix operators and helping lemmas **)
// TODO: Needs to be instanciated differently
assume MaxUint32: FStar.UInt.max_int 32 = 4294967295

let op_Hat_Greater_Greater (a: u32) (b: u32): Pure u32
  (requires True)
  (ensures (fun c -> v c = (v a / (pow2 (v b))))) =
  op_Greater_Greater_Hat a b

let op_Hat_Star (a: u32) (b: u32): Pure u32
  (requires (FStar.UInt.size (v a * v b) 32))
  (ensures (fun c -> v a * v b = v c)) =
  op_Star_Hat a b

let op_Hat_Slash a b = op_Slash_Hat a b
let op_Hat_Percent a b = op_Percent_Hat a b

let op_Greater_Greater_Greater (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in
  (op_Greater_Greater_Hat a s) |^ (a <<^ (m -^ s))

let op_Less_Less_Less (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in  
  (op_Less_Less_Hat a s) |^ (op_Greater_Greater_Hat a (m -^ s))

(* Chacha 20 code *)
val quarter_round: m:u32s{length m >= 16} -> a:u32{v a < 16} -> b:u32{v b<16} -> c:u32{v c<16} -> 
  d:u32{v d<16} -> STL unit
  (requires (fun h -> live h m)) 
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  write_32 m a (read_32 m a +%^ read_32 m b);
  write_32 m d (read_32 m d ^^ read_32 m a);
  let (tmp:u32) = read_32 m d in 
  write_32 m d (tmp <<< UInt32.uint_to_t 16); 
  write_32 m c (read_32 m c +%^ read_32 m d); 
  write_32 m b (read_32 m b ^^ read_32 m c); 
  let tmp = read_32 m b in
  write_32 m b (tmp <<< UInt32.uint_to_t 12);
  write_32 m a (read_32 m a +%^ read_32 m b); 
  write_32 m d (read_32 m d ^^ read_32 m a); 
  let tmp = read_32 m d in
  write_32 m d (tmp <<< UInt32.uint_to_t 8);
  write_32 m c (read_32 m c +%^ read_32 m d); 
  write_32 m b (read_32 m b ^^ read_32 m c); 
  let tmp = read_32 m b in
  write_32 m b (tmp <<< UInt32.uint_to_t 7)

(* Chacha20 block function *)
val column_round: m:u32s{length m >= 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let column_round m =
  quarter_round m 0ul 4ul 8ul 12ul;
  quarter_round m 1ul 5ul 9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

val diagonal_round: m:u32s{length m >= 16} -> STL unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul 8ul 13ul;
  quarter_round m 3ul 4ul 9ul 14ul

val xor_bytes_2: output:bytes -> in1:bytes{disjoint in1 output} -> 
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_bytes_2 output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = len -^ 1ul in
      let in1i = read_8 in1 i in
      let oi   = read_8 output i in
      let oi   = UInt8.logxor in1i oi in
      write_8 output i oi;
      xor_bytes_2 output in1 i
    end

#reset-options "--z3timeout 50"

val chacha20_init: state:u32s{length state >= 16} -> key:bytes{length key = 32 /\ disjoint state key} ->
  counter:u32 -> iv:UInt64.t -> constant:UInt32.t -> STL unit
  (requires (fun h -> live h state /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let chacha20_init state key counter iv constant =
  (* Key part *)
  let k = bytes_to_u32s key in
  assert(length k = 8);
  (* Nonce part *)
  let n0 = Int.Cast.uint64_to_uint32 iv in
  let n1 = Int.Cast.uint64_to_uint32 (UInt64.shift_right iv 32ul) in
  (* Constant part *)
  write_32 state 0ul 0x61707865ul;
  write_32 state 1ul 0x3320646eul;
  write_32 state 2ul 0x79622d32ul;
  write_32 state 3ul 0x6b206574ul;
  (* Update with key *)
  write_32 state 4ul  (read_32 k 0ul);
  write_32 state 5ul  (read_32 k 1ul);
  write_32 state 6ul  (read_32 k 2ul);
  write_32 state 7ul  (read_32 k 3ul);
  write_32 state 8ul  (read_32 k 4ul);
  write_32 state 9ul  (read_32 k 5ul);
  write_32 state 10ul (read_32 k 6ul);
  write_32 state 11ul (read_32 k 7ul);
  (* Block counter part *)
  write_32 state 12ul counter; 
  (* Update with nonces *)
  write_32 state 13ul (constant);
  write_32 state 14ul (n0);
  write_32 state 15ul (n1)

#reset-options

val sum_matrixes: new_state:u32s{length new_state >= 16} -> old_state:u32s{length old_state >= 16 /\ disjoint new_state old_state} -> STL unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  write_32 m 0ul (read_32 m 0ul +%^ read_32 m0 0ul); 
  write_32 m 1ul (read_32 m 1ul +%^ read_32 m0 1ul);
  write_32 m 2ul (read_32 m 2ul +%^ read_32 m0 2ul);
  write_32 m 3ul (read_32 m 3ul +%^ read_32 m0 3ul);
  write_32 m 4ul (read_32 m 4ul +%^ read_32 m0 4ul);
  write_32 m 5ul (read_32 m 5ul +%^ read_32 m0 5ul);
  write_32 m 6ul (read_32 m 6ul +%^ read_32 m0 6ul);
  write_32 m 7ul (read_32 m 7ul +%^ read_32 m0 7ul); 
  write_32 m 8ul (read_32 m 8ul +%^ read_32 m0 8ul);
  write_32 m 9ul (read_32 m 9ul +%^ read_32 m0 9ul); 
  write_32 m 10ul (read_32 m 10ul +%^ read_32 m0 10ul);
  write_32 m 11ul (read_32 m 11ul +%^ read_32 m0 11ul);
  write_32 m 12ul (read_32 m 12ul +%^ read_32 m0 12ul);
  write_32 m 13ul (read_32 m 13ul +%^ read_32 m0 13ul);
  write_32 m 14ul (read_32 m 14ul +%^ read_32 m0 14ul);
  write_32 m 15ul (read_32 m 15ul +%^ read_32 m0 15ul);
  ()

#reset-options "--z3timeout 50"

val chacha20_update: output:bytes -> state:u32s{length state >= 32 /\ disjoint state output} ->
  len:u32{v len <= 64 /\ length output >= v len} -> STL unit
    (requires (fun h -> live h state /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_update output state len =
  if UInt32.eq len 64ul then begin
    (* General case *)
    (* Initial state stored inplace *)
    let m = state in
    let m0 = bytes_to_u32s output in
    assert(length output >= 64); 
    assert(length m0 >= 16);
    memcpy_32 m 0ul m0 0ul 16ul;
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
    sum_matrixes m0 m
  end
  else begin
    (* Initial state *) 
    let m = sub_32 state 0ul 16ul in
    let m0 = sub_32 state 16ul 16ul in
    memcpy_32 m 0ul m0 0ul 16ul;
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
    let m = u32s_to_bytes m in
    memcpy_8 m 0ul output 0ul len
  end

#reset-options

val chacha20_loop:
  state:u32s{length state >= 32} -> key:bytes{length key = 32 /\ disjoint state key} -> 
  counter:UInt32.t -> iv:UInt64.t ->  constant:UInt32.t -> plaintext:bytes{disjoint state plaintext} -> 
  ciphertext:bytes{disjoint state ciphertext /\ disjoint key ciphertext /\ disjoint plaintext ciphertext} -> j:u32 -> max:u32{v j <= v max /\ v counter + v max < pow2 n} -> STL unit
    (requires (fun h -> live h state /\ live h key /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (v max-v j) * 64  /\ length ciphertext >= (v max-v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))
let rec chacha20_loop state key counter iv constant plaintext ciphertext j max =
  if j =^ max then ()
  else 
    begin
      (* Generate new state for block *)
      let cipher_block = sub_8 ciphertext 0ul 64ul in
      let ciphertext' = sub_8 ciphertext 64ul (64ul ^* (max -^ j -^ 1ul)) in
      let plain_block = sub_8 plaintext 0ul 64ul in
      let plaintext' = sub_8 plaintext 64ul (64ul ^* (max -^ j -^ 1ul)) in
      chacha20_init state key (counter +^ j) iv constant;
      chacha20_update cipher_block state 64ul;
      (* XOR the key stream with the plaintext *)
      xor_bytes_2 cipher_block plain_block 64ul;
      (* Apply Chacha20 to the next blocks *)
      chacha20_loop state key counter iv constant plaintext' ciphertext' (j +^ 1ul) max
    end

#reset-options "--z3timeout 50"

val chacha20_encrypt_body: state:u32s{length state = 32} -> 
  ciphertext:bytes{disjoint state ciphertext} -> 
  key:bytes{length key = 32 /\ disjoint ciphertext key /\ disjoint key state} -> 
  counter:u32 -> iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint state plaintext} -> 
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h state /\ live h ciphertext /\ live h key /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1))
let chacha20_encrypt_body state ciphertext key counter iv constant plaintext len =
  let max = (len ^/ 64ul) in
  let rem = len ^% 64ul in
  (* Apply Chacha20 max times **)  
  chacha20_loop state key counter iv constant plaintext ciphertext 0ul max;
  if rem =^ 0ul then ()
  else 
    begin 
      let cipher_block = sub_8 ciphertext (UInt32.mul 64ul max) rem in 
      let plain_block = sub_8 plaintext (UInt32.mul 64ul max) rem in 
      chacha20_init state key (counter +^ max) iv constant;
      chacha20_update cipher_block state rem;
      xor_bytes_2 cipher_block plain_block rem
    end

val chacha20_encrypt: ciphertext:bytes -> key:bytes{length key = 32 /\ disjoint ciphertext key} -> 
  counter:u32 -> iv:UInt64.t -> constant:UInt32.t ->
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint key plaintext} ->
  len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let chacha20_encrypt ciphertext key counter iv constant plaintext len = 
  push_frame ();
  let state = create_32 32ul in
  (* Compute number of iterations *)
  chacha20_encrypt_body state ciphertext key counter iv constant plaintext len;
  pop_frame()
