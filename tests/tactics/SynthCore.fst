module SynthCore

open FStar.Tactics.V2

(* A synthesis at a proof goal is run by Core, on the goal it computes in
   its context: here, the branch condition [x > 0] is a hypothesis. *)
let in_context (x:int) : int =
  if x > 0 then (let _ : squash (x > 0) = _ by (smt ()) in x) else 0

[@@expect_failure [19]]
let bad : squash False = _ by (idtac ())

(* The result of a synthesis at another type is checked by Core. *)
let witness : x:int{x > 0} = _ by (exact (`1))

(* Synthesis is supported only in top-level let definitions. *)
[@@expect_failure [12]]
val v : synth_by_tactic #Type0 (fun () -> exact (`int))
