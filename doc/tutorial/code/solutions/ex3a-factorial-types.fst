module Factorial

(* Here are some other types for factorial:
    val factorial: nat -> Tot nat
    val factorial: nat -> Tot (x:int{x > 0})
    val factorial: int -> int
    val factorial: int -> x:int{x > 0}  *)
val factorial: x:int{x>=0} -> Tot int
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)
