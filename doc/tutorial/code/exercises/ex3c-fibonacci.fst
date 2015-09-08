module Ex3cFibonacci

(* Try proving a monotonicity property for the fibonacci function. *)

// BEGIN: FibonacciIncreasing
val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_increasing : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// END: FibonacciIncreasing
let fibonacci_increasing n = ()
