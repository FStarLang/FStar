(* Model implementation of FStar.Stubs.Tactics.Types: verified, but never extracted (the real implementation is native). *)
module FStar.Stubs.Tactics.Types

open FStar.Stubs.Reflection.Types

noeq type goal =
  | MkGoal : env -> typ -> term -> bool -> string -> goal

noeq type proofstate =
  | MkProofstate : list goal -> list goal -> proofstate

let ref_proofstate = bool

let goals_of (MkProofstate gs _) = gs
let smt_goals_of (MkProofstate _ gs) = gs

let goal_env     (MkGoal e _ _ _ _) = e
let goal_type    (MkGoal _ t _ _ _) = t
let goal_witness (MkGoal _ _ w _ _) = w
let is_guard     (MkGoal _ _ _ b _) = b
let get_label    (MkGoal _ _ _ _ l) = l
let set_label l (MkGoal e t w b _) = MkGoal e t w b l

let incr_depth ps = ps
let decr_depth ps = ps
let tracepoint _ = true
let set_proofstate_range ps _ = ps

let tref _ = bool
