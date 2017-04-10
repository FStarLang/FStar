module Ex03a
//factorial-types

open FStar.Mul

(* What are some other types you can give to factorial?
   Try writing them and see if F* agrees with you. *)

// BEGIN: FactorialTypes
val factorial: x:int{x>=0} -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))
// END: FactorialTypes

