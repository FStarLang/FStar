module Crypto.Symmetric.GF128.Spec

open Crypto.Symmetric.Bytes 

type text = Seq.seq (lbytes 16)
type elem = lbytes 16 (* use instead a bit vector? *) 

assume val op_Plus_At: elem -> elem -> Tot elem
assume val op_Star_At: elem -> elem -> Tot elem

let zero = Seq.create 16 0uy 

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

let encode (x:lbytes 16): elem = x

val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = SeqProperties.head vs in 
    (encode v +@ poly (SeqProperties.tail vs) r ) *@ r

let finish a s = a +@ s 
let mac vs r s = finish (poly vs r) s

