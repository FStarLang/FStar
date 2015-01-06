module Factorial

(* What are some other types you can give to factorial?
   Try writing them and see if F* agrees with you. *)
val factorial: x:int{x>=0} -> Tot int
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)
