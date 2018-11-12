(* Expect 5 intentional failures *)
module TestSet
assume type elt
assume val a : elt
assume val b : elt
assume val c : elt
assume AB_distinct: a=!=b
open FStar.TSet

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (mem b (union (singleton a) (singleton b)));
  assert (mem a (union (singleton a) (singleton b)));
  assert (subset (singleton a) (union (singleton a) (singleton b)));
  assert (subset (singleton b) (union (singleton a) (singleton b)));
  assert (equal (union (singleton a) (singleton b))
                (union (singleton b) (singleton a)))

