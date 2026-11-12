module IfaceInstCache

(* The instances are declared in the interface, and defined here without the
   attribute. Resolving [c int] while checking [c_bool] must not leave a stale
   instance cache in which [c_bool] is missing. *)
let c_int : c int = { v = 1 }
let c_bool : c bool = { v = v #int }

let t = v #bool
