module Crypto.Symmetric.GF128

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.UInt8
open FStar.Int.Cast
open FStar.Buffer

module U32 = FStar.UInt32
type u32 = FStar.UInt32.t

type bytes = buffer byte

let len = 16ul // length of GF128 in bytes
type elem = b:bytes {length b = UInt32.v len } 

(* * Every block of message is regarded as an element in Galois field GF(2^128), **)
(* * it is represented as 16 bytes. The following several functions are basic    **)
(* * operations in this field.                                                   **)
(* * gf128_add: addition. Equivalent to bitxor.                                  **)
(* * gf128_shift_right: shift right by 1 bit. Used in multiplication.            **)
(* * gf128_mul: multiplication. Achieved by combining 128 additions.             **)

//16-09-23 we still miss a math specification of GF128 and a correctness proof.

(* Every function "func_name_loop" is a helper for function "func_name". *)

private val gf128_add_loop: 
  a:elem -> b:elem {disjoint a b} -> 
  dep:u32{U32(dep <=^ len)} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let rec gf128_add_loop a b dep =
  if dep <> 0ul then begin
    let i = U32 (dep -^ 1ul) in
    a.(i) <- a.(i) ^^ b.(i);
    gf128_add_loop a b i
  end

(* In place addition. Calculate "a + b" and store the result in a. *)
val gf128_add: a:elem -> b:elem {disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let gf128_add a b = gf128_add_loop a b len

private val gf128_shift_right_loop: a:elem -> dep:u32{U32(dep <^ len)} -> Stack unit
  (requires (fun h -> live h a))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let rec gf128_shift_right_loop a dep =
  if dep = 0ul 
  then a.(0ul) <- shift_right a.(0ul) 1ul
  else begin
    let i = U32 (dep -^ 1ul) in
    a.(dep) <- (a.(i) <<^ 7ul) +%^ (a.(dep) >>^ 1ul);
    gf128_shift_right_loop a i
  end

(* In place shift. Calculate "a >> 1" and store the result in a. *)
private val gf128_shift_right: a:elem -> Stack unit
  (requires (fun h -> live h a))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let gf128_shift_right a = gf128_shift_right_loop a 15ul

(* Generate mask. If the i-th bit of num is 1 then return 11111111, otherwise return 00000000. *)
private val ith_bit_mask: num:byte -> i:u32{U32.v i < 8} -> Tot byte
let ith_bit_mask num i =
  let proj = shift_right 128uy i in
  let res = logand num proj in
  eq_mask res proj

private val apply_mask_loop: a:elem -> m:elem {disjoint a m} -> msk:byte -> dep:u32{U32.v dep <= 16} -> Stack unit
  (requires (fun h -> live h a /\ live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let rec apply_mask_loop a m msk dep =
  if dep <> 0ul then 
  begin
    let i = U32 (dep -^ 1ul) in
    m.(i) <- a.(i) &^ msk;
    apply_mask_loop a m msk i
  end

(* This will apply a mask to each byte of bytes. *)
(* Mask a with msk, and store the result in m. *)
private val apply_mask: a:elem -> m:elem {disjoint a m} -> msk:byte -> Stack unit
  (requires (fun h -> live h a /\ live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let apply_mask a m msk = apply_mask_loop a m msk len

private let r_mul = 225uy

private val gf128_mul_loop: 
  a:elem -> b:elem {disjoint a b} -> tmp:bytes {length tmp = 32 /\ disjoint a tmp /\ disjoint b tmp} -> 
  dep:u32{U32.v dep <= 128} -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h tmp))
  (ensures (fun h0 _ h1 -> live h1 a /\ live h1 tmp /\ modifies_2 a tmp h0 h1))
let rec gf128_mul_loop a b tmp dep =
  if dep <> 128ul then 
  begin
    let r = sub tmp 0ul len in
    let m = sub tmp len len in
    let num = b.(U32 (dep /^ 8ul)) in
    let msk = ith_bit_mask num (U32.rem dep 8ul) in
    apply_mask a m msk;
    gf128_add r m;
    let num = a.(15ul) in
    let msk = ith_bit_mask num 7ul in
    gf128_shift_right a;
    let num = a.(0ul) in
    a.(0ul) <- (num ^^ (logand msk r_mul));
    gf128_mul_loop a b tmp (U32 (dep +^ 1ul))
  end

(* In place multiplication. Calculate "a * b" and store the result in a.    *)
(* WARNING: may have issues with constant time. *)
val gf128_mul: a:elem -> b:elem {disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let gf128_mul a b =
  push_frame();
  let tmp = create 0uy 32ul in
  gf128_mul_loop a b tmp 0ul;
  blit tmp 0ul a 0ul 16ul;
  pop_frame()

let add_and_multiply a e k = 
  gf128_add a e;
  gf128_mul a k


  
//16-09-23 Instead of the code below, we should re-use existing AEAD encodings
//16-09-23 and share their injectivity proofs and crypto model.

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val ghash_loop_: 
  tag:elem ->
  auth_key:elem {disjoint tag auth_key} ->
  str:bytes{disjoint tag str /\ disjoint auth_key tag} ->
  len:u32{length str = U32.v len} ->
  dep:u32{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> U32.v len - U32.v dep <= 16 /\ live h tag /\ live h auth_key /\ live h str))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let ghash_loop_ tag auth_key str len dep =
  push_frame();
  let last = create 0uy 16ul in
  blit str dep last 0ul (U32 (len -^ dep)); 
  add_and_multiply tag last auth_key;
  pop_frame()

(* WARNING: may have issues with constant time. *)
private val ghash_loop: 
  tag:elem ->
  auth_key:elem {disjoint tag auth_key} ->
  str:bytes{disjoint tag str /\ disjoint auth_key tag} ->
  len:u32{length str = U32.v len} ->
  dep:u32{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> live h tag /\ live h auth_key /\ live h str))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let rec ghash_loop tag auth_key str len dep =
  (* Appending zeros if the last block is not a complete one. *)
  let rest = U32(len -^ dep) in 
  if rest <> 0ul then 
  if U32 (16ul >=^ rest) then ghash_loop_ tag auth_key str len dep
  else 
  begin
    let next = U32.add dep 16ul in
    let si = sub str dep 16ul in
    add_and_multiply tag si auth_key;
    ghash_loop tag auth_key str len next
  end
 
(* During authentication, the length information should also be included. *)
(* This function will generate an element in GF128 by:                    *)
(* 1. express len of additional data and len of ciphertext as 64-bit int; *)
(* 2. concatenate the two integers to get a 128-bit block.                *)
private val mk_len_info: len_info:bytes{length len_info = 16} ->
    len_1:u32 -> len_2:u32 -> Stack unit
    (requires (fun h -> live h len_info))
    (ensures (fun h0 _ h1 -> live h1 len_info /\ modifies_1 len_info h0 h1))
let mk_len_info len_info len_1 len_2 =
  let last = shift_left (uint32_to_uint8 len_1) 3ul in
  let open FStar.UInt32 in
  upd len_info 7ul last;
  let len_1 = len_1 >>^ 5ul in
  upd len_info 6ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 5ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 4ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 3ul (uint32_to_uint8 len_1);
  let last = FStar.UInt8 (uint32_to_uint8 len_2 <<^ 3ul) in
  upd len_info 15ul last;
  let len_2 = len_2 >>^ 5ul in
  upd len_info 14ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 13ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 12ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 11ul (uint32_to_uint8 len_2)
// relying on outer initialization?

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(* A hash function used in authentication. It will authenticate additional data first, *)
(* then ciphertext and at last length information. The result is stored in tag.        *)
val ghash:
  k:elem ->
  ad:bytes{disjoint k ad} ->
  adlen:u32{U32.v adlen = length ad} ->
  ciphertext:bytes{disjoint k ciphertext /\ disjoint ad ciphertext} ->
  len:u32{U32.v len = length ciphertext} ->
  tag:elem{disjoint k tag /\ disjoint ad tag /\ disjoint ciphertext tag} ->
  Stack unit
  (requires (fun h -> live h k /\ live h ad /\ live h ciphertext /\ live h tag))
  (ensures (fun h0 _ h1 -> live h1 tag /\ modifies_1 tag h0 h1))

let ghash k ad adlen ciphertext len tag =
  push_frame();
  let h0 = ST.get() in
  let len_info = create (0uy) 16ul in
  mk_len_info len_info adlen len;
  let h1 = ST.get() in
  assert(modifies_0 h0 h1);
  fill tag 0uy 16ul;
  ghash_loop tag k ad adlen 0ul;
  ghash_loop tag k ciphertext len 0ul;
  add_and_multiply tag len_info k;
  //gf128_add tag len_info;
  //gf128_mul tag k;
  let h2 = ST.get() in
  assert(modifies_1 tag h1 h2);
  pop_frame()
