module Plugin.Tactic.Test
open FStar.Tactics
open Plugin.Tactic
let go () =
  assert_by_tactic (id 1000 = 1000) test
