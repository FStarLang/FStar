module Ex3cFibonacci

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_increasing : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// BEGIN: FibonacciIncreasingProof
let rec fibonacci_increasing n =
  match n with
  | 2 -> ()
  | _ -> fibonacci_increasing (n-1)
// END: FibonacciIncreasingProof
