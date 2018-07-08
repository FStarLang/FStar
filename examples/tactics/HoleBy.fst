module HoleBy

open FStar.Tactics

let x : int = _ by (exact (`1))
let _ = assert (x == 1)

[@(expect_failure [228])]
let _ : int = _ by (exact (`1); fail "")

[@(expect_failure [228])]
let lem1 x = () <: squash (x + 1 == 1 + x)
                by fail ""

val lem2 : (x:int) -> (y:int) -> Lemma (x + y == y + x)
let lem2 x y =
    () <: _ by smt ()

val lem3 : (x:int) -> (y:int) -> Lemma (x + y == y + x)
[@(expect_failure [228])]
let lem3 x y =
    () <: _ by fail ""
