module IfaceLetInterleaved

(* A definition of the interface that sits between two `val`s comes into scope
   in the implementation exactly when the to-do list reaches it: after [f] has
   been implemented, and before [h] is. *)

val f (x:int) : int

let g (x:int) : int = f x + 1

val h (x:int) : int
