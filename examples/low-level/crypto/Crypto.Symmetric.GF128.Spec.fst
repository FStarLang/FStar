module Crypto.Symmetric.GF128.Spec

open Crypto.Symmetric.Bytes 

module U128 = FStar.UInt128

type text = Seq.seq (lbytes 16)
type elem = U128.t

val op_Plus_At: elem -> elem -> Tot elem
let op_Plus_At x y = U128.(x ^^ y)

val op_Star_At: elem -> elem -> Tot elem
let op_Star_At x y = U128.(x ^^ y) // FAKE IMPLEMENTATION TODO FIX

assume val add_comm: a:elem -> b:elem -> Lemma (a +@ b == b +@ a)

val zero: elem
let zero = FStar.Int.Cast.uint64_to_uint128(0uL)

val encode:lbytes 16 -> Tot elem
let encode b = zero // FAKE IMPLEMENTATION TODO FIX
val decode:elem -> Tot (lbytes 16)
let decode e = Seq.create 16 0uy



(*
val add_loop: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)


val add_loop: l:nat{ l <= 16 } -> lbytes l -> lbytes l -> Tot (lbytes l)
let rec add_loop l a b = 
  if l = 0 then Seq.createEmpty 
  else
    let r = add_loop (l-1) (tail a) (tail b) in 
    cons (UInt8.logxor (head a) (head b)) r

let op_Plus_At a b = add_loop 16 a b
*)

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

let mac vs r s = (finish (poly vs r) s)


val poly_cons: x:lbytes 16 -> xs:text -> r:elem ->
  Lemma (poly (SeqProperties.cons x xs) r == (encode x +@ poly xs r) *@ r)
let poly_cons x xs r =
  let xxs = SeqProperties.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (SeqProperties.tail xxs) xs

val poly_empty: t:text{Seq.length t == 0} -> r:elem ->
  Lemma (poly t r == zero)
let poly_empty t r = ()
