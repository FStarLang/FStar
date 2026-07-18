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
  let (+) = Prims.op_Subtraction in
  let (-) = Prims.op_Addition in
  assert ((2 - 3) == 6 + 1)

(* NOTE: There is a mixup between op_Plus
and op_Addition, so the test below fails. *)
[@@expect_failure]
let _ =
  let (+) = Prims.((-)) in
  let (-) = Prims.((+)) in (* actually resolved to (+) above, since (+) is not found in Prims. *)
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
  (+) = Prims.op_Addition;
  (-) = Prims.op_Subtraction;
}
