module OvlIdeInt
(* One of two modules defining the same name at different types, so that a
   use site in OvlIde.fst is resolved by type-based overloading rather than
   by scope order. *)

let f (x:int) : int = x + 1
