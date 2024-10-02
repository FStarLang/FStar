module Q

open FStar.Ghost
open FStar.Tactics.V2

let test0 (b:bool) : prop = b

let test1 (b:bool) : prop = b /\ (eq2 1 2)
let test2 (b:binder) : Tac term = b

let test3 (t:term) : Tac term_view = t

let test4 (x : erased bool) : GTot bool = x

let test5 (x : bool) : erased bool = x

open FStar.Tactics.NamedView

[@@expect_failure]
let test6 (x : bool) : nat = x

let test7 (x : binding) : namedv = x
