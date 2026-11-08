module IfaceInstOrder
open IfaceInstClass
(* IfaceInstGeneric is a dependency of the implementation only, so it is
   loaded after the interface. The interface instance must still take
   precedence, as it is defined later in this module. *)
open IfaceInstGeneric
let test () = assert (f (3 <: int) == 1)
