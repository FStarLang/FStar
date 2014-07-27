
module Test.Testing

let a = (1>2) && (3<=4) || (2<1) && (9>=1)
let b = let x = 1 in let y=2 in let z=x+y in z*z/(x+y)
//let c = let b = ref 0 in b := 1 ; !b
let d = (1, not true, 2)
let x = -1 + 2/3 * 5 % 2 - 3
let e = if a then b else x
let z = "100€ \"easy \\win\"\x05"

val fib : int -> int
let rec fib n = match n with
 | 0 -> 1 | 1 -> 1
 | _ -> (fib (n-1)) + (fib (n-2))

let u = fib 10
let v x y = x+y
let w = v 0 1
