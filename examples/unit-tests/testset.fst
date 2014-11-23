(* Expect 3 intentional failures *)
module TestSet
assume type elt
assume logic val A : elt
assume logic val B : elt
assume logic val C : elt
assume AB_distinct: A=!=B
open Set

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (mem B (union (singleton A) (singleton B)));
  assert (mem A (union (singleton A) (singleton B)));
  assert (Subset (singleton A) (union (singleton A) (singleton B)));
  assert (Subset (singleton B) (union (singleton A) (singleton B)));
  assert (equal (union (singleton A) (singleton B))
                (union (singleton B) (singleton A)))

val should_fail1: unit -> Tot unit
let should_fail1 u =
  assert (mem B (singleton A))

val should_fail2: unit -> Tot unit
let should_fail2 u = 
  assert (Subset (union (singleton A) (singleton B)) (singleton A))

val should_fail3: unit -> Tot unit
let should_fail3 u =
  assert (mem C (union (singleton A) (singleton B)))
            
