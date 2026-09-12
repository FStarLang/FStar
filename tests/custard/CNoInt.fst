module CNoInt

(* Prims.int is unbounded, so it has no C type.  The direct-to-C backend has to
   say so (error 367) rather than silently pick a width. *)

let add (x:int) (y:int) : int = x + y

let main () : int = add 2 3
