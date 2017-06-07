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

let _ =
    let x = 1 in
    assert_by_tactic trefl (1 == x)

let va1    = assert_by_tactic trefl (1 == 1)
let va2 () = assert_by_tactic trefl (1 == 1)
let va3    = fun () -> assert_by_tactic trefl (1 == 1)

type t =
    | A : t
    | B : t
    | C : t
    | D : x:int -> t

let f x =
    match x with
    | A -> A
    | B -> B
    | C -> C
    | D x -> D x

let g (x : t) = f (f (f (f (f (f x)))))

let _ = assert_by_tactic trivial (g A == (f (g A)))
let _ = assert_by_tactic trivial (f B == B)

let _ = assert_by_tactic trivial (A? A == true)
let _ = assert_by_tactic trivial (D? (D 5) == true)
let _ = assert_by_tactic trivial (D?.x (D 5) == 5)
