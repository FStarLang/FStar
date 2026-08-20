module OvlBool
(* The other one. Opened after OvlInt, so these names win by default. *)

type t = | B of bool

let f (x:bool) : bool = not x
let g (x:bool) (y:bool) : bool = x && y
let mk (x:bool) : t = B x
let id (x:bool) : bool = x
