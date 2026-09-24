module KrmlUnit

(* Issue #4583.  --custard_unit only populates the unit interfaces for the
   direct C backend, so on KrmlC it must be refused (error 155) rather than
   accepted and silently ignored. *)

let main () : bool = true
