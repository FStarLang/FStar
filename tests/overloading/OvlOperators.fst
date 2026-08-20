module OvlOperators

(* Operators get no special treatment in overload resolution. An
   operator is mangled into an ordinary identifier -- ( + ) into op_Plus,
   ( ~- ) into op_Tilde_Minus -- and from then on it is resolved exactly
   like any other name: Prims declares ( + ) on int, this module declares
   ( + ) on vec, and the two are candidates for the same name. *)

type vec = | V of int & int

let ( + ) (a b : vec) : vec =
  let V (x1, y1) = a in
  let V (x2, y2) = b in
  V (x1 + x2, y1 + y2)

let ( - ) (a b : vec) : vec =
  let V (x1, y1) = a in
  let V (x2, y2) = b in
  V (x1 - x2, y1 - y2)

let vsum = V (1, 2) + V (3, 4)
let vdiff = V (3, 4) - V (1, 2)

(* Prims.( + ) and Prims.( - ) are reachable even though this module
   declares its own. *)
let isum : int = 1 + 2
let idiff : int = 3 - 1

(* Prefix minus is the separate operator ( ~- ), which this module does
   not declare, so it is not overloaded at all. *)
let ineg : int = - 3
