(* The two primitives Pulse.Lib.Core declares and does not define.  Custard
   emits them as externals; this file is the OCaml realization. *)

let fork_core f = ignore (Domain.spawn f)

let hide_div f = f ()
