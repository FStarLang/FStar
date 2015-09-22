module BugTot

val test1 : nat -> nat -> Tot nat
let rec test1 x y = if x = 0 then y else test1 0 y

val test2 : nat -> Tot (nat -> Tot nat)
let rec test2 x y = if x = 0 then y else test2 0 y

val test3 : nat -> Tot ( nat -> Dv nat)
let rec test3 x y = if x = 0 then y else test3 0 y
