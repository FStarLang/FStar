module Ex3cFibonacci

(* Try proving a monotonicity property for the fibonacci function. *)

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_monotone : n:nat{True} -> Lemma (False)
let fibonacci_monotone n = ()
