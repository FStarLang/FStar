module Crypto.Symmetric.GF128

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U128 = FStar.UInt128
module BV   = FStar.BitVector
module Spec = Crypto.Symmetric.GF128.Spec

open U8
open Spec
open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.Int.Cast
open FStar.Buffer

module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Spec = Crypto.Symmetric.GF128.Spec
open Spec

private inline_for_extraction let len = 16ul // length of GF128 in bytes

type elem = Spec.elem
type elemB = b:buffer U128.t{length b = 1}

let sel_elem h (b:elemB{live h b}): GTot elem = Seq.index (as_seq h b) 0

#set-options "--z3rlimit 20 --max_fuel 0 --initial_fuel 0"

inline_for_extraction val load128_be: b:buffer U8.t{length b = 16} -> Stack U128.t
  (requires (fun h -> live h b))
  (ensures (fun h0 n h1 -> h0 == h1 /\ live h1 b /\
    n = encode (as_seq h1 b)))
let load128_be b = Crypto.Symmetric.Bytes.load_big128 len b (*
  let b1 = sub b 0ul 8ul in
  let b2 = sub b 8ul 8ul in
  let l1 = C.load64_be b1 in
  let i1 = uint64_to_uint128 l1 in
  let l2 = C.load64_be b2 in
  let i2 = uint64_to_uint128 l2 in
  let b = U128.(i1 <<^ 64ul) in
  U128.(b |^ i2) *)

inline_for_extraction val store128_be: b:buffer U8.t{length b = 16} -> i:U128.t -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\
    Seq.equal (decode i) (as_seq h1 b)))
let store128_be b i = 
  Crypto.Symmetric.Bytes.store_big128 len b i;
  let h = ST.get() in
  Crypto.Symmetric.Bytes.lemma_big_endian_inj (decode i) (as_seq h b)
  (*
  let b1 = sub b 0ul 8ul in
  let b2 = sub b 8ul 8ul in
  let i1 = uint128_to_uint64 (U128.(i >>^ 64ul)) in
  let i2 = uint128_to_uint64 i in
  C.store64_be b1 i1;
  C.store64_be b2 i2*)


(* * Every block of message is regarded as an element in Galois field GF(2^128), **)
(* * it is represented as 16 bytes. The following several functions are basic    **)
(* * operations in this field.                                                   **)
(* * gf128_add: addition. Equivalent to bitxor.                                  **)
(* * gf128_shift_right: shift right by 1 bit. Used in multiplication.            **)
(* * gf128_mul: multiplication. Achieved by combining 128 additions.             **)

(* In place addition. Calculate "a + b" and store the result in a. *)
inline_for_extraction val gf128_add: a:elemB -> b:elemB {disjoint a b} -> Stack unit
  (requires (fun h -> live h a /\ live h b))
  (ensures (fun h0 _ h1 -> 
    live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1 /\
    sel_elem h1 a = sel_elem h0 a +@ sel_elem h0 b))
let gf128_add a b = 
  let av = a.(0ul) in
  let bv = b.(0ul) in
  let r = U128.(av ^^ bv) in
  a.(0ul) <- r

inline_for_extraction let one_128 = uint64_to_uint128(1uL)
inline_for_extraction let zero_128 = uint64_to_uint128(0uL)

private let r_mul = U128.(uint64_to_uint128(225uL) <<^ 120ul)

private val elem_vec_logand_lemma: a:BV.bv_t 128 -> i:nat{i < 128} ->
  Lemma (Seq.equal (BV.logand_vec a (BV.elem_vec #128 i))
    (if Seq.index a i then (BV.elem_vec #128 i) else (BV.zero_vec #128)))
let elem_vec_logand_lemma a i = ()

private inline_for_extraction 
val ith_bit_mask: num:U128.t -> i:U32.t{U32.v i < 128} -> Tot (r:U128.t{r = Spec.ith_bit_mask num (U32.v i)})
let ith_bit_mask num i =
  let mi = U32.(127ul -^ i) in
  let proj = U128.(one_128 <<^ mi) in
  FStar.Math.Lemmas.pow2_lt_compat 128 (U32.v mi);
  FStar.Math.Lemmas.small_modulo_lemma_1 (pow2 (U32.v mi)) (pow2 128);
  assert(U128.v proj = (FStar.UInt.pow2_n #128 (127 - U32.v i)));
  assert(Seq.equal (FStar.UInt.to_vec #128 (U128.v proj)) (BV.elem_vec #128 (U32.v i)));
  let res = U128.(num &^ proj) in
  elem_vec_logand_lemma (FStar.UInt.to_vec #128 (U128.v num)) (U32.v i);
  U128.(eq_mask res proj)

#reset-options "--z3rlimit 20 --max_fuel 1 --initial_fuel 1"

private val gf128_mul_loop: 
  x:elemB -> 
  y:elemB {disjoint x y} -> 
  z:elemB {disjoint x z /\ disjoint y z} ->
  ctr:U32.t{U32.v ctr <= 128} -> 
  Stack unit
  (requires (fun h -> live h x /\ live h y /\ live h z))
  (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h0 z /\
    live h1 x /\ live h1 y /\ live h1 z /\ modifies_2 x z h0 h1 /\
    sel_elem h1 z = Spec.mul_loop (sel_elem h0 x) (sel_elem h0 y) (sel_elem h0 z) (U32.v ctr)))
let rec gf128_mul_loop x y z ctr =
  if ctr <> 128ul then 
  begin
    let xv = x.(0ul) in
    let yv = y.(0ul) in
    let zv = z.(0ul) in

    let mski = ith_bit_mask yv ctr in     
    let msk_x = U128.(xv &^ mski) in
    z.(0ul) <- U128.(zv ^^ msk_x);
    
    let msk0 = ith_bit_mask xv 127ul in
    let msk_r_mul = U128.(r_mul &^ msk0) in
    let xv = x.(0ul) in
    let xv = U128.(xv >>^ 1ul) in
    x.(0ul) <- U128.(xv ^^ msk_r_mul);

    gf128_mul_loop x y z (U32.(ctr +^ 1ul))
  end

(* In place multiplication. Calculate "a * b" and store the result in a.    *)
(* WARNING: may have issues with constant time. *)
val gf128_mul: x:elemB -> y:elemB {disjoint x y} -> Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 x /\ live h1 y /\ modifies_1 x h0 h1 /\
    sel_elem h1 x = sel_elem h0 x *@ sel_elem h0 y))
let gf128_mul x y =
  push_frame();
  let z = create zero_128 1ul in
  gf128_mul_loop x y z 0ul;
  x.(0ul) <- z.(0ul);
  pop_frame()


val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block}
  -> k:elemB{disjoint acc k /\ disjoint block k} -> Stack unit
  (requires (fun h -> live h acc /\ live h block /\ live h k))
  (ensures (fun h0 _ h1 -> live h0 acc /\ live h0 block /\ live h0 k
    /\ live h1 acc /\ live h1 k
    /\ modifies_1 acc h0 h1
    /\ sel_elem h1 acc = (sel_elem h0 acc +@ sel_elem h0 block) *@ sel_elem h0 k))
let add_and_multiply acc block k =
  gf128_add acc block;
  gf128_mul acc k


val finish: acc:elemB -> s:buffer UInt8.t{length s = 16} -> Stack unit
  (requires (fun h -> live h acc /\ live h s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> live h0 acc /\ live h0 s
    /\ modifies_1 acc h0 h1 /\ live h1 acc
    /\ decode (sel_elem h1 acc) = finish (sel_elem h0 acc) (as_seq h0 s)))
let finish a s = 
  //let _ = IO.debug_print_string "finish a=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer a 0ul 16ul in
  //let _ = IO.debug_print_string "finish s=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer s 0ul 16ul in
  let sf = load128_be s in
  a.(0ul) <- U128.(a.(0ul) ^^ sf)
  //let _ = IO.debug_print_string "finish a=" in 
  //let _ = Crypto.Symmetric.Bytes.print_buffer a 0ul 16ul in



(*
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
  let t = sub str dep (U32.(len -^ dep)) in
  tmp.(0ul) <- load128_be t;
  add_and_multiply tag tmp auth_key

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
    tmp.(0ul) <- load128_be si;
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
*)
