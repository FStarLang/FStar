module FStar.Tactics.Types

open FStar.Reflection.Types

assume new type proofstate
assume new type goal

(* Returns the active goals *)
val goals     : proofstate -> list goal
(* Returns the goals marked for SMT *)
val smtgoals : proofstate -> list goal

(* Inspecting a goal *)
val goal_env     : goal -> env
val goal_type    : goal -> typ
val goal_witness : goal -> term

(* Tracing *)
val incr_depth : proofstate -> proofstate
val decr_depth : proofstate -> proofstate
val tracepoint : proofstate -> unit
val set_proofstate_range : proofstate -> FStar.Range.range -> proofstate

type direction =
    | TopDown
    | BottomUp

type guard_policy =
    | SMT
    | Goal
    | Force
    | Drop // unsound! careful!
