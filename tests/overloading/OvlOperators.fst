module OvlOperators

(* Operators get no special treatment in resolution: once the name has
   been mangled they behave like any other symbol. What is special is
   that the Prims lid an operator falls back to used to be reachable
   *only* when the operator was not in scope, so a user-defined ( + )
   hid integer addition entirely. It is now the last candidate. *)

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

(* Prims.op_Addition and Prims.op_Subtraction are still reachable. *)
let isum : int = 1 + 2
let idiff : int = 3 - 1

(* And so is the unary minus, which mangles to a different name. *)
let ineg : int = - 3
