module UnitTests

open FStar.Tactics

let _ = assert_by_tactic trivial True
let _ = assert_by_tactic trivial (1 + 1 = 2)
let _ = assert_by_tactic trivial (1 + 1 == 2)
let _ = assert_by_tactic trivial ("a" ^ "b" = "ab")
let _ = assert_by_tactic trivial ("a" ^ "b" == "ab")

let phi = True

let _ = assert_by_tactic trivial phi

let rec fib n =
    if n < 2
    then n
    else fib (n-1) + fib (n-2)

let _ = assert_by_tactic trivial (fib 5 = 5)
let _ = assert_by_tactic trivial (fib 5 == 5)

type t = | A | B | C | D
let f x = match x with
| A -> A
| B -> B
| C -> C
| D -> D

let g (x : t) = f (f (f (f (f (f x)))))

let a = assert_by_tactic trivial (g A == (f (g A)))
let b = assert_by_tactic trivial (f B == B)
