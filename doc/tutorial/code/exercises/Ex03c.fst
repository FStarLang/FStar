module Ex03c
//fibonacci-property


(* Try proving a property for the fibonacci function. *)

// BEGIN: FibonacciGreaterThanArg
val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// END: FibonacciGreaterThanArg
let fibonacci_greater_than_arg n = admit() //replace the admit() by a valid proof.
