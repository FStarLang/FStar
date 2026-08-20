module Operators

(* Checking we can re-bind - *)
let _ =
  let (-) = Prims.((+)) in
 assert ((2 - 3) == 5)

(* Checking we can re-bind + *)
let _ =
  let (+) = Prims.((-)) in
  assert ((2 + 3) == (-1))

(* Both. *)
let _ =
  let (+) = Prims.op_Minus in
  let (-) = Prims.op_Plus in
  assert ((2 - 3) == 6 + 1)

(* Operator names are mangled uniformly, so Prims.((+)) and Prims.((-))
resolve to the addition and subtraction of Prims, and are not confused
with the locally-bound operators. *)
let _ =
  let (+) = Prims.((-)) in
  let (-) = Prims.((+)) in
  assert ((2 - 3) == 6 + 1)

noeq
type ops = {
  (+) : Prims.int -> Prims.int -> Prims.int;
  (-) : Prims.int -> Prims.int -> Prims.int;
}

class arith (a:Type) = {
  (+) : a -> a -> a;
  (-) : a -> a -> a;
}

instance _ : arith int = {
  (+) = Prims.op_Plus;
  (-) = Prims.op_Minus;
}

(* Prefix minus is the operator ( ~- ), as in OCaml, but "-" remains the
usual notation for it. *)
let _ = assert (forall (x:int). -x == ~-x)
let _ = assert (forall (x:int). -x == Prims.op_Tilde_Minus x)
let _ = assert (forall (x y:int). x - -y == x + y)
let neg (x:int) = -x
let _ = assert (neg 7 == -7)

(* And it can be defined for other types. *)
noeq type vec = | V : int -> int -> vec
let ( ~- ) (v:vec) : vec = let V x y = v in V ~-x ~-y
(* Note: ( ~- ) is now shadowed for the rest of the module, so we cannot
write -1 for the integer literal here. *)
let _ = assert (-(V 1 2) == V (0-1) (0-2))
