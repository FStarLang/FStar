module Ex3cFibonacci

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_monotone : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// BEGIN: FibonacciMonotoneProof
let rec fibonacci_monotone n =
  match n with
  | 2 | 3 -> ()
  | _ -> fibonacci_monotone (n-1)
// END: FibonacciMonotoneProof
