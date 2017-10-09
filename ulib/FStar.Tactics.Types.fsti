module FStar.Tactics.Types

assume new type proofstate

val incr_depth : proofstate -> proofstate
val decr_depth : proofstate -> proofstate
val tracepoint : proofstate -> unit

type direction =
    | TopDown
    | BottomUp
