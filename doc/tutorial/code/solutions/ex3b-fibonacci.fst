module Fibonacci

(* val fibonacci : nat -> Tot nat *)
(* val fibonacci : int -> int *)
(* val fibonacci : int -> ML int (same as above) *)
val fibonacci : int -> Tot (x:nat{x>0})
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)
