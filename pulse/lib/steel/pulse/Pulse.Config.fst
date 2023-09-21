module Pulse.Config

open FStar.Tactics.V2

(* This is currently unused, we use the --ext option instead. *)
let join_goals : bool = false

let debug_flag (s:string) : Tac bool =
  let v = ext_getv ("pulse:" ^ s) in
  v <> "" && v <> "0" && v <> "false"
