module NormVsSMT

let _ = assert_norm (True /\ True)
let _ = assert_norm (True \/ True)

(* These fail, and probably shouldn't, but it's not too worrysome *)
(* let _ = assert (c_and True True) *)
(* let _ = assert (c_and c_True c_True) *)

val l1 : (a : Type) -> Lemma (a ==> squash a)
let l1 a = assert_norm (a ==> squash a)

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
let _ = assert_norm (exists (x:int). x >= 0)
// Apparently z3 can't show `exists (x:nat). x >= 0`, probably the refinement getting in the way
