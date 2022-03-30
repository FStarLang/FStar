#light "off"
module FStar.Tactics.Printing

open FStar.Tactics.Types

(* Dump a proofstate into the CLI or Emacs *)
val do_dump_proofstate     : proofstate -> string -> unit

(* Only for deubgging *)
val goal_to_string         : string -> option<(int * int)> -> proofstate -> goal -> string
val goal_to_string_verbose : goal -> string
