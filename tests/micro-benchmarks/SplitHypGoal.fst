module SplitHypGoal

(* When a query is split into goals, a goal that is literally one of its
   hypotheses is discharged without asking the solver.  These check that a
   goal which only resembles a hypothesis still reaches the solver. *)

let same (x y:int) : Lemma (requires x == 1 /\ y == 2) (ensures y == 2 /\ x == 1) = ()

let branch (b:bool) (x:int)
  : Lemma (requires x == 1) (ensures (if b then x == 1 else ~ b)) = ()

[@@expect_failure [19]]
let other_constant (x:int) : Lemma (requires x == 1) (ensures x == 2) = ()

[@@expect_failure [19]]
let other_variable (x y:int) : Lemma (requires x == 1 /\ y == 2) (ensures y == 1) = ()

(* The inner [x] is a different variable from the outer one. *)
[@@expect_failure [19]]
let shadowed () : Lemma (forall (x:int). x == 1 ==> (forall (x:int). x == 1)) = ()

[@@expect_failure [19]]
let other_branch (b:bool) (x:int)
  : Lemma (requires x == 1) (ensures (if b then x == 1 else x == 3)) = ()

[@@expect_failure [19]]
let under_match (o:option int)
  : Lemma (requires Some? o ==> Some?.v o == 1)
          (ensures (match o with Some v -> v == 2 | None -> True)) = ()

[@@expect_failure [19]]
let other_type (x:nat) (y:int)
  : Lemma (requires y == x) (ensures (y <: int) == (x + 1 <: int)) = ()
