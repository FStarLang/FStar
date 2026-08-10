module Reify
open FStar.Tactics.V2

(* Section 7.4: [Tac] is compiled through its representation type
   [ref_proofstate -> Dv a], not by dropping the effect.  The proofstate has to
   be threaded, or the compiler's tactic engine and the tactics it runs would
   disagree about the calling convention of every metaprogram. *)
let add (x:int) : Tac int = x + 1

let twice (x:int) : Tac int = add (add x)

let main () : FStar.All.ML unit = FStar.IO.print_string "ok\n"
