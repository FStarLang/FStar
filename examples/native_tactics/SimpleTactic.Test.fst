module SimpleTactic.Test
open FStar.Tactics
open SimpleTactic
let go () =
  assert_by_tactic (id 1000 = 1000) test
