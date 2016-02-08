(* Expect 5 intentional failures *)
module TestSet
assume type elt
assume logic val a : elt
assume logic val b : elt
assume logic val c : elt
assume AB_distinct: a=!=b
open FStar.Set

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (mem b (union (singleton a) (singleton b)));
  assert (mem a (union (singleton a) (singleton b)));
  assert (subset (singleton a) (union (singleton a) (singleton b)));
  assert (subset (singleton b) (union (singleton a) (singleton b)));
  assert (Equal (union (singleton a) (singleton b))
                (union (singleton b) (singleton a)))

