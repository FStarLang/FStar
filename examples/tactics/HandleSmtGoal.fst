module HandleSmtGoal

open FStar.Tactics

[@@ handle_smt_goals]
let tac () : Tac unit =
  dump "now"

let f (x:int) : Pure unit (requires x == 2) (ensures fun _ -> True) =
  assert (x == 2);
  ()

(* A bogus lemma, used only to obtain a simple goal that will not be solvable
   if handle_smt_goal does not trigger. It also has a trivially true precondition,
   but that is sent to SMT*)
assume
val test_lemma (_:unit) : Lemma (requires forall (x:nat). x >= 0) (ensures False)

[@@ handle_smt_goals]
let tac2 () : Tac unit =
  apply_lemma (`test_lemma)

let g () : Tot unit =
  assert (False)
