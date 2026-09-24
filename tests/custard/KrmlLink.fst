module KrmlLink

(* Issue #4583.  As KrmlUnit, for --custard_link on KrmlRust.  The rejection
   comes before any linked interface is loaded, so the file need not exist. *)

let main () : bool = true
