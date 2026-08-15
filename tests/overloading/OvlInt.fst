module OvlInt
(* One of two modules that define the same names at different types. *)

type t = | I of int

let f (x:int) : int = x + 1
let g (x:int) (y:int) : int = x + y
let mk (x:int) : t = I x
let id (x:int) : int = x
