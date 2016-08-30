module Ex03b
//fibonacci


(* Provide several types for the fibonacci function *)
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

