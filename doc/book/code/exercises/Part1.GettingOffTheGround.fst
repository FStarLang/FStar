module Part1.GettingOffTheGround

let incr (x:int) : int = x + 1

val max (x:int) (y:int) : int
let max = admit() //remove the admit and write a definition

open FStar.Mul
val factorial (n:nat) : nat //replace this `val` with some others
let rec factorial n
  = if n = 0
    then 1
    else n * factorial (n - 1)

val fibonacci (n:nat) : nat //replace this `val` with some others
let rec fibonacci n
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)
