module Fibonacci

(* val fibonacci : nat -> Tot nat *)
(* val fibonacci : int -> int *)
(* val fibonacci : int -> ML int (same as above) *)
let rec fibonacci n =
  if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2)
