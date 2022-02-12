module HandleSmtGoal

open FStar.Tactics

[@@ resolve_implicits; handle_smt_goals]
let tac () : Tac unit =
  dump "now"

let f (x:int) : Pure unit (requires x == 2) (ensures fun _ -> True) =
  assert (x == 2);
  ()
