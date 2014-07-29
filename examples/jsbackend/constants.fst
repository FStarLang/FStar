
module JSUnit

let a = (1>2) && (3<=4) || (2<1) && (9>=1)
let b = let x = 1 in let y=2 in let z=x+y in z*z/(x+y)
let x = -1 + 2/3 * 5 % 2 - 3
let e = if a then b else x
let z = "\\u20ac"

let nil = 
        JS.utest "SimpleArith" b 3 ;
        JS.utest "IfThenElse" e (-2)
