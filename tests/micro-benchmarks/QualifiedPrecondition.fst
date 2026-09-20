module QualifiedPrecondition

(* [comp_requires] decides whether a [requires] clause is trivial, and
   [desugar_comp] decides the same thing again once the clause is desugared.
   The two must agree, or a definition acquires an assertion in its body for a
   precondition that its type says is the caller's obligation.  Comparing the
   last component of the name against "True" or "l_True" does not agree: the
   name below is neither [Prims.l_True] nor provable, and [f] was rejected with
   Error 19 for failing to prove it. *)

let l_True = False

let f (x:int) : Pure int (requires QualifiedPrecondition.l_True) = 0

(* ... and it really is the caller's obligation. *)
[@@expect_failure [19]]
let caller () : int = f 0

(* The surface [True], and [Prims.l_True] spelled out, are both trivial. *)
let g (x:int) : Pure int (requires True) (ensures fun y -> y == 0) = 0
let h (x:int) : Pure int (requires Prims.l_True) (ensures fun y -> y == 0) = 0
