//SNIPPET_START: sample
module Part1.GettingOffTheGround

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

//SNIPPET_START: max
val max (x:int) (y:int) : int
let max x y = if x >= y then x else y

val max1 (x:int) (y:int)
  : z:int{ z >= x && z >= y && (z = x || z = y)}
let max1 x y = if x >= y then x else y

let max2 (x:int) (y:int)
  : z:int{ z = max x y }
  = if x > y
    then x
    else y
//SNIPPET_END: max

//SNIPPET_START: factorial
open FStar.Mul
let rec factorial (n:nat)
  : nat
  = if n = 0
    then 1
    else n * factorial (n - 1)
//SNIPPET_END: factorial

//SNIPPET_START: factorial_answers
let rec factorial1 (n:nat)
  : int
  = if n = 0
    then 1
    else n * factorial1 (n - 1)

let rec factorial2 (n:nat)
  : y:int{y>=1}
  = if n = 0
    then 1
    else n * factorial2 (n - 1)
//SNIPPET_END: factorial_answers


//SNIPPET_START: fibonacci
let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)
//SNIPPET_END: fibonacci

//SNIPPET_START: fibonacci_answers
val fibonacci_1 : x:int -> y:int{y >= 1 /\ y >= x /\ (if x>=3 then y >= 2 else true)}
let rec fibonacci_1 n =
  if n <= 1 then 1 else fibonacci_1 (n - 1) + fibonacci_1 (n - 2)

(* Try these other types too *)
(* val fibonacci_1 : int -> int *)
(* val fibonacci_1 : int -> nat *)
(* val fibonacci_1 : int -> y:int{y>=1} *)
(* val fibonacci_1 : x:int -> y:int{y>=1 /\ y >= x} *)
(* val fibonacci_1 : int -> Tot (x:nat{x>0}) *)
//SNIPPET_END: fibonacci_answers
