module IfaceInstOrder
open IfaceInstClass
(* A more specific instance, declared in the interface. *)
instance specific : c int = { f = (fun _ -> 1) }
