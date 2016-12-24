module Crypto.Symmetric.GF128

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.UInt8
open FStar.Int.Cast
open FStar.Buffer

module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Spec = Crypto.Symmetric.GF128.Spec
open Spec

let len = 16ul // length of GF128 in bytes

type elem = Spec.elem 
type elemB = b:buffer U128.t{length b = 1}

let load128_le b = 
    let b1 = sub b 0ul 8ul in
    let b2 = sub b 8ul 8ul in
    let l1 = C.load64_le b1 in
    let i1 = uint64_to_uint128 l1 in
    let l2 = C.load64_le b2 in
    let i2 = uint64_to_uint128 l2 in
    let b = U128.(i2 <<^ 64ul) in
    U128.(b +^ i1)


let store128_le b i = 
    let b1 = sub b 0ul 8ul in
    let b2 = sub b 8ul 8ul in
    let i1 = uint128_to_uint64 (U128.(i >>^ 64ul)) in
    let i2 = uint128_to_uint64 i in
    C.store64_le b1 i2;
    C.store64_le b2 i1


(* * Every block of message is regarded as an element in Galois field GF(2^128), **)
(* * it is represented as 16 bytes. The following several functions are basic    **)
(* * operations in this field.                                                   **)
(* * gf128_add: addition. Equivalent to bitxor.                                  **)
(* * gf128_shift_right: shift right by 1 bit. Used in multiplication.            **)
(* * gf128_mul: multiplication. Achieved by combining 128 additions.             **)

//16-09-23 we still miss a math specification of GF128 and a correctness proof.

(* In place addition. Calculate "a + b" and store the result in a. *)
val gf128_add: a:elemB -> b:elemB {disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> 
    live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1))
let gf128_add a b = 
  let av = a.(0ul) in
  let bv = b.(0ul) in
  let r = U128.(av ^^ bv) in
  a.(0ul) <- r 

(* In place shift. Calculate "a >> 1" and store the result in a. *)
private val gf128_shift_right: a:elemB -> Stack unit
  (requires (fun h -> live h a))
  (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let gf128_shift_right a = 
  let av = a.(0ul) in
  let a' = U128.(av >>^ 1ul) in
  a.(0ul) <- a'


let one_128 = uint64_to_uint128(1uL)
let zero_128 = uint64_to_uint128(0uL)
private let r_mul = U128.(uint64_to_uint128(225uL) <<^ 120ul)

(* Generate mask. If the i-th bit of num is 1 then return 11111111, otherwise return 00000000. *)
private val ith_bit_mask: num:U128.t -> i:U32.t{U32.v i < 128} -> Tot U128.t
let ith_bit_mask num i =
  let mi = U32.(127ul -^ i) in
  let proj = U128.(one_128 <<^ mi) in
  let res = U128.(num &^ proj) in
  U128.(eq_mask res proj)

private val zero_bit_mask: num:U128.t -> Tot U128.t
let zero_bit_mask num =
  let proj = U128.(one_128) in
  let res = U128.(num &^ proj) in
  U128.(eq_mask res proj)

val gf128_mul_loop: 
  x:elemB -> 
  v:elemB {disjoint x v} -> 
  z:elemB {disjoint x z /\ disjoint v z} ->
  ctr:U32.t{U32.v ctr <= 128} -> 
  Stack unit
  (requires (fun h -> live h x /\ live h v /\ live h z))
  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 v /\ live h1 z /\ modifies_2 v z h0 h1))
let rec gf128_mul_loop x v z ctr =
  if ctr <> 128ul then 
  begin
    let xv = x.(0ul) in
    let vv = v.(0ul) in
    let zv = z.(0ul) in

    let mski = ith_bit_mask xv ctr in     
    let msk_v = U128.(vv &^ mski) in
    z.(0ul) <- U128.(zv ^^ msk_v);

    let msk0 = zero_bit_mask vv in
    let msk_r_mul = U128.(r_mul &^ msk0) in
    gf128_shift_right v;
    let vv = v.(0ul) in
    v.(0ul) <- U128.(vv ^^ msk_r_mul);
    gf128_mul_loop x v z (U32.(ctr +^ 1ul))
  end

(* In place multiplication. Calculate "a * b" and store the result in a.    *)
(* WARNING: may have issues with constant time. *)
val gf128_mul: x:elemB -> y:elemB {disjoint x y} -> Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> 
    live h1 x /\ live h1 y /\ modifies_1 x h0 h1))
let gf128_mul x y =
  let h0 = ST.get() in
  push_frame();
  let z = create zero_128 1ul in
  gf128_mul_loop y x z 0ul;
  x.(0ul) <- z.(0ul);
  pop_frame()


val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block}
  -> k:elemB{disjoint acc k /\ disjoint block k} -> Stack unit
  (requires (fun h -> live h acc /\ live h block /\ live h k))
  (ensures (fun h0 _ h1 -> live h0 acc /\ live h0 block /\ live h0 k
    /\ live h1 acc /\ live h1 k
    /\ modifies_1 acc h0 h1
    /\ get h1 acc 0 == (get h0 acc 0) +@ (get h0 block 0) *@ (get h0 k 0)))
let add_and_multiply acc block k =
  gf128_add acc block;
  gf128_mul acc k


val finish: acc:elemB -> s:buffer UInt8.t{length s = 16} -> Stack unit
  (requires (fun h -> live h acc /\ live h s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> live h0 acc /\ live h0 s
    /\ modifies_1 acc h0 h1 /\ live h1 acc
    /\ decode (get h1 acc 0) == finish (get h0 acc 0) (as_seq h0 s)))
let finish a s = 
  //let _ = IO.debug_print_string "finish a=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer a 0ul 16ul in
  //let _ = IO.debug_print_string "finish s=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer s 0ul 16ul in
  let sb = create zero_128 1ul in
  sb.(0ul) <- load128_le s;
  gf128_add a sb
  //let _ = IO.debug_print_string "finish a=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer a 0ul 16ul in


//16-09-23 Instead of the code below, we should re-use existing AEAD encodings
//16-09-23 and share their injectivity proofs and crypto model.

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val ghash_loop_:
  tag:elemB ->
  auth_key:elemB {disjoint tag auth_key} ->
  str:buffer UInt8.t{disjoint tag str /\ disjoint auth_key tag} ->
  tmp:buffer UInt128.t{disjoint tag tmp /\ disjoint auth_key tmp /\ disjoint str tmp} ->
  len:U32.t{length str = U32.v len} ->
  dep:U32.t{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> U32.v len - U32.v dep <= 16 /\ live h tag /\ live h auth_key /\ live h str))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let ghash_loop_ tag auth_key str tmp len dep =
  push_frame();
  let t = create 0uy 16ul in
  blit str dep t 0ul (U32.(len -^ dep));
  tmp.(0ul) <- load128_le t;
  add_and_multiply tag tmp auth_key;
  pop_frame()

(* WARNING: may have issues with constant time. *)
private val ghash_loop: 
  tag:elemB ->
  auth_key:elemB {disjoint tag auth_key} ->
  str:buffer UInt8.t{disjoint tag str /\ disjoint auth_key str} ->
  tmp:buffer UInt128.t{disjoint tag tmp /\ disjoint auth_key tmp /\ disjoint str tmp} ->
  len:U32.t{length str = U32.v len} ->
  dep:U32.t{U32.v dep <= U32.v len} -> Stack unit
  (requires (fun h -> live h tag /\ live h auth_key /\ live h str /\ live h tmp))
  (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ live h1 tmp /\ modifies_2 tag tmp h0 h1))
let rec ghash_loop tag auth_key str tmp len dep =
  (* Appending zeros if the last block is not complete *)
  let rest = U32.(len -^ dep) in 
  if rest <> 0ul then 
  if U32.(16ul >=^ rest) then ghash_loop_ tag auth_key str tmp len dep
  else 
  begin
    let next = U32.add dep 16ul in
    let si = sub str dep 16ul in
    tmp.(0ul) <- load128_le si;
    add_and_multiply tag tmp auth_key;
    ghash_loop tag auth_key str tmp len next
  end
 
(* During authentication, the length information should also be included. *)
(* This function will generate an element in GF128 by:                    *)
(* 1. express len of additional data and len of ciphertext as 64-bit int; *)
(* 2. concatenate the two integers to get a 128-bit block.                *)
private val mk_len_info: len_info:elemB ->
    len_1:U32.t -> len_2:U32.t -> Stack unit
    (requires (fun h -> live h len_info))
    (ensures (fun h0 _ h1 -> live h1 len_info /\ modifies_1 len_info h0 h1))
let mk_len_info len_info len_1 len_2 =
  let l1 = uint64_to_uint128(uint32_to_uint64 len_1) in
  let l2 = uint64_to_uint128(uint32_to_uint64 len_2) in
  let u = U128.((l1 <<^ 64ul) +^ l2) in
  len_info.(0ul) <- u

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* A hash function used in authentication. It will authenticate additional data first, *)
(* then ciphertext and at last length information. The result is stored in tag.        *)
val ghash:
  k:elemB ->
  ad:buffer UInt8.t{disjoint k ad} ->
  adlen:U32.t{U32.v adlen = length ad} ->
  ciphertext:buffer UInt8.t{disjoint k ciphertext /\ disjoint ad ciphertext} ->
  len:U32.t{U32.v len = length ciphertext} ->
  tag:elemB{disjoint k tag /\ disjoint ad tag /\ disjoint ciphertext tag} ->
  Stack unit
  (requires (fun h -> live h k /\ live h ad /\ live h ciphertext /\ live h tag))
  (ensures (fun h0 _ h1 -> live h1 tag /\ modifies_1 tag h0 h1))

let ghash k ad adlen ciphertext len tag =
  push_frame();
  let h0 = ST.get() in
  let len_info = create zero_128 1ul in
  mk_len_info len_info adlen len;
  let h1 = ST.get() in
  assert(modifies_0 h0 h1);
  tag.(0ul) <- zero_128;
  let tmp = create zero_128 1ul in
  ghash_loop tag k ad tmp adlen 0ul;
  ghash_loop tag k ciphertext tmp len 0ul;
  add_and_multiply tag len_info k;
  //gf128_add tag len_info;
  //gf128_mul tag k;
  let h2 = ST.get() in
  assert(modifies_1 tag h1 h2);
  pop_frame()
