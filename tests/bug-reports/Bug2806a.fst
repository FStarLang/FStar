module Bug2806a

open FStar.Real
open FStar.Tactics

let one = 1.0R
let oone = 01.0R

[@@expect_failure]
let bad () : Lemma False =
  assert (~(one == oone)) by (compute ())
