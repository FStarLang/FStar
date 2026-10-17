(* The primitive Pulse.Lib.Core declares and does not define.  Custard
   emits it as an external; this file is the OCaml realization. *)

let fork_core f = ignore (Domain.spawn f)

