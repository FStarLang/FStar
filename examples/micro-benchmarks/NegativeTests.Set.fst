(* ******************************************************************************** *)
module NegativeTests.Set
assume type elt
assume val a : elt
assume val b : elt
assume val c : elt
assume AB_distinct: a=!=b
open FStar.TSet

val should_fail1: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail1 u =
  assert (mem b (singleton a))

val should_fail2: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail2 u =
  assert (subset (union (singleton a) (singleton b)) (singleton a))

val should_fail3: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail3 u =
  assert (mem c (union (singleton a) (singleton b)))
