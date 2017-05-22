#light "off"
module FStar.Tactics.Native

val register_tactic_dumb: string -> unit
val register_tactic: string -> 'a -> unit
val find_tactic: string -> unit
// val from_tactic_1: tactic<'a> -> tac<'a>