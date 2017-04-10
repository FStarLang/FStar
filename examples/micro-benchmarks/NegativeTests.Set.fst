(* ******************************************************************************** *)
module NegativeTests.Set
assume type elt
assume logic val a : elt
assume logic val b : elt
assume logic val c : elt
assume AB_distinct: a=!=b
open FStar.TSet

val should_fail1: unit -> Tot unit
let should_fail1 u =
  assert (mem b (singleton a))

val should_fail2: unit -> Tot unit
let should_fail2 u =
  assert (subset (union (singleton a) (singleton b)) (singleton a))

val should_fail3: unit -> Tot unit
let should_fail3 u =
  assert (mem c (union (singleton a) (singleton b)))
