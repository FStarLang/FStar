module Crypto.Symmetric.GF128.Spec

open Crypto.Symmetric.Bytes
open FStar.Int.Cast
open FStar.UInt128
open FStar.UInt

type text = Seq.seq (lbytes 16)
type elem = FStar.UInt128.t

val op_Plus_At: elem -> elem -> Tot elem
let op_Plus_At x y = x ^^ y

let ones_128 = uint_to_t (ones 128)
let zero_128 = uint_to_t (zero 128)

noextract val ith_bit_mask: num:elem -> i:nat{i < 128} -> Tot (r:elem{
    nth (v num) i = true ==> r = ones_128 /\
    nth (v num) i = false ==> r = zero_128})
let ith_bit_mask num i = if (nth (v num) i) then ones_128 else zero_128

val shift_right: elem -> Tot elem
let shift_right a = a >>^ 1ul

private let r_mul = uint64_to_uint128(225uL) <<^ 120ul

val mask_add: a:elem -> b:elem -> r:elem -> dep:nat{dep < 128} -> Tot (s:elem{
    nth (v b) dep = true ==> s = r +@ a /\
    nth (v b) dep = false ==> s = r}) (decreases (128 - dep))
let mask_add a b r dep =
  let msk = ith_bit_mask b dep in
  let m = a &^ msk in
  r +@ m

val shift_right_modulo: a:elem -> Tot (r:elem{
    nth (v a) 127 = true ==> r = (shift_right a) +@ r_mul /\
    nth (v a) 127 = false ==> r = shift_right a})
let shift_right_modulo a =
  let msk = ith_bit_mask a 127 in
  let m = r_mul &^ msk in
  shift_right a +@ m

#set-options "--z3rlimit 15 --max_fuel 1 --initial_fuel 1"

val mul_loop: a:elem -> b:elem -> r:elem -> dep:nat{dep <= 128} -> Tot elem
  (decreases (128 - dep))
let rec mul_loop a b r dep =
  if dep = 128 then r else
  begin
    let nr = mask_add a b r dep in 
    let na = shift_right_modulo a in
    mul_loop na b nr (dep + 1)
  end

val op_Star_At: a:elem -> b:elem -> Tot elem
let op_Star_At a b = mul_loop a b zero_128 0

val add_comm: a:elem -> b:elem -> Lemma (a +@ b == b +@ a)
let add_comm a b = logxor_commutative (v a) (v b)

val zero: elem
let zero = FStar.Int.Cast.uint64_to_uint128(0uL)

noextract val encode: lbytes 16 -> Tot elem
let encode b = uint_to_t (big_endian b)
noextract val decode: elem -> Tot (lbytes 16)
let decode e = big_bytes 16ul (v e)

open FStar.Seq
open FStar.SeqProperties 

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = SeqProperties.head vs in 
    (encode v +@ poly (SeqProperties.tail vs) r ) *@ r

let finish a s = decode (a +@ (encode s))

let mac vs r s = finish (poly vs r) s

val poly_cons: x:lbytes 16 -> xs:text -> r:elem ->
  Lemma (poly (SeqProperties.cons x xs) r == (encode x +@ poly xs r) *@ r)
let poly_cons x xs r =
  let xxs = SeqProperties.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (SeqProperties.tail xxs) xs

val poly_empty: t:text{Seq.length t == 0} -> r:elem ->
  Lemma (poly t r == zero)
let poly_empty t r = ()
