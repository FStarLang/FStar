module FStar.Tactics.Types

assume new
type proofstate 

val incr_depth: proofstate -> proofstate
val decr_depth: proofstate -> proofstate
val tracepoint: proofstate -> unit
val set_proofstate_range: proofstate -> FStar.Range.range -> proofstate

type direction =
  | TopDown
  | BottomUp

type guard_policy =
  | SMT
  | Goal
  | Force
  // unsound! careful!
  | Drop

