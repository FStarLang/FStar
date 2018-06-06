module NormVsSMT

let _ = assert_norm (True /\ True)
let _ = assert_norm (True \/ True)

(* These fail, and probably shouldn't, but it's not too worrysome *)
(* let _ = assert (c_and True True) *)
(* let _ = assert (c_and c_True c_True) *)

(* This fails after removing t_valid, c.f. 5ac0bd96d *)
(* val l1 : (a : Type) -> Lemma (a ==> squash a) *)
(* let l1 a = assert_norm (a ==> squash a) *)

val l2 : (a : Type) -> Lemma (squash a ==> a)
let l2 a = assert_norm (squash a ==> a)

// Why does the third one need SMT and not the second? Investigate
let _ = assert_norm (1 = 1)
let _ = assert_norm (1 == 1)
let _ = assert_norm (1 === 1)

let _ = assert_norm True
let _ = assert_norm (False ==> True)
let _ = assert_norm (False ==> False)
let _ = assert_norm (forall (x:nat). x >= 0)
let trigger (x:int) = True
let _ = assert (trigger 0); assert (exists (x:int).{:pattern (trigger x)} x >= 0)
// NS: 02/11 Apparently z3 can't show `exists (x:int). x >= 0`, after a change to encode unit-typed terms as unit
// Apparently z3 can't show `exists (x:nat). x >= 0`, probably the refinement getting in the way
