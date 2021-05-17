//SNIPPET_START: sample
module Sample

let incr (x:int) : int = x + 1
//SNIPPET_END: sample

//SNIPPET_START: ex1.1
let incr1 (x:int) : y:int{y > x} = x + 1
//SNIPPET_END: ex1.1

//the expect_failure attribute tells F* to check that "Error 19" is
//raised on the next definition, to suppress an error report, and
//proceed with the rest of the file.
[@@expect_failure [19]]
//SNIPPET_START: ex1.2
let incr2 (x:int) : nat = x + 1
//SNIPPET_END: ex1.2

//SNIPPET_START: ex1.3
let incr3 (x:nat) : nat = x + 1
//SNIPPET_END: ex1.3

//SNIPPET_START: ex1.4
val incr4 (x:int) : int
let incr4 x = x + 1
//SNIPPET_END: ex1.4

//SNIPPET_START: incr_types
let incr5 (x:int) : y:int{y = x + 1} = x + 1
let incr6 (x:int) : y:int{x = y - 1} = x + 1
let incr7 (x:int) : y:int{if x%2 = 0 then y%2 = 1 else y%2 = 0} = x + 1
//SNIPPET_END: incr_types

val max (x:int) (y:int) : int
let max x y = if x >= y then x else y

val max1 (x:int) (y:int)
  : z:int{ z >= x && z >= y && (z = x || z = y)}
let max1 x y = if x >= y then x else y

let max2 (x:int) (y:int)
  : z:int{ z = max x y }
  = if x > y then x else y

//SNIPPET_START: factorial
open FStar.Mul
let rec factorial (n:nat)
  : nat
  = if n = 0 then 1 else n * factorial (n - 1)
//SNIPPET_END: factorial
