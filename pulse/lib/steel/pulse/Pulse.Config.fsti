module Pulse.Config

open FStar.Tactics.V2

val join_goals : bool

(* Checks if a boolean debug flag `s` is enabled, i.e.
if the extension option `pulse:s` was given, and its value
is not "0" or "false". *)
val debug_flag : string -> Tac bool
