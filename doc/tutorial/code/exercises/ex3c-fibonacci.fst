module Ex3cFibonacci

(* Try proving a monotonicity property for the fibonacci function. *)

// BEGIN: FibonacciMonotone
val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_monotone : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// END: FibonacciMonotone
let fibonacci_monotone n = ()
