module Bug1389C

open FStar.Ghost
open FStar.Seq
open FStar.Ref

type t = (s:seq (ref int){length s > 0})

let contains (s:t) (x:ref int) : GTot Type0 =
  (exists (i:nat{i < length s}). index s i == x)

let foo (s:t) (x:ref int{s `contains` x}) :
  GTot (unit * seq (ref int))
    (decreases (length s)) // This decreases turns the GTot into GHOST internally, exposing the bug
  = (), s

val fail: es:erased t -> x:ref int{Ghost.reveal es `contains` x} ->
  Tot (erased t)
let fail es x =
  let es = elift2_p foo es (Ghost.hide x) in
  assert (False); // this DEFINITELY should NOT go through
  es // this should NOT type check
