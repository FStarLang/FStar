module Bug025

val length: list 'a -> nat
let rec length = function
 | [] -> 0
 | x::xs -> 1 + (length xs)
