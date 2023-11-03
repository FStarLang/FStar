module TypeclassesWithRefinements
open FStar.Tactics.Typeclasses

class eq a = {
    deq : a -> a -> bool
}

instance eq_int : eq int = {
    deq = ( = )
}

//works in master
let test (x y : int) = deq x y

//meet of refinments here picks x:int { True \/ y > x} ~ int
//works in master
let test2 (x:int) (y:int{y > x}) = deq x y

//Similar meet, but this time it picks x:int { True \/ x > 0} ~ int
//works in master
let test3 (x:int{x > 0}) (y:int) = deq x y

//This time the meet is non-trivial, since
//it is x:int{ x > 0 \/ y > x}
//and typeclass resolution fails
//** fails in master
let test4 (x:int{x > 0}) (y:int{y > x}) = deq x y

//similar to test3
//works in master
let test5 (x:nat) (y:int) = deq x y

//no instance for nat
[@@expect_failure]
let test6 (x:nat) (y:nat) = deq x y

instance eq_nat : eq nat = {
    deq = ( = )
}

let pos = x:nat { x > 0}
//works in master with nat
let test7 (x:nat) (y:pos { y > 17 }) = deq x y
//fails in master
let test8 (x:nat{ x > 2 }) (y:pos { y > 17 }) = deq x y

class neg a = {
    dneg : a -> a
}

instance neg_bool : neg bool = {
    dneg = fun x -> not x
}

let tneg (x:bool) = dneg x
//fails in master
let tneg2 (x:bool { x = true }) = dneg x