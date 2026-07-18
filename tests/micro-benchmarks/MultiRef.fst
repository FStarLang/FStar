module MultiRef

(* The refinement is present only in the binder for y. *)
let sub (x y : int{x >= y}) : nat =
  x - y

val sub2 (x y : int{x >= y}) : nat
let sub2 x y = x - y

// Multibinders are not supported here, regardless
// of the refinement.
// val sub3 : (x y : int{x >= y}) -> nat
// let sub3 x y = x - y
