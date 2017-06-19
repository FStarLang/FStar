module Simplifier

open FStar.Tactics
open FStar.Tactics.Simplifier

let goal_is_true : tactic unit =
    g <-- cur_goal;
    match term_as_formula g with
    | True_ -> trivial
    | _ -> fail "not syntactically true"

let test_simplify : tactic unit =
    simplify;;
    or_else goal_is_true (dump "";; fail "simplify left open goals")

let _ = assert_by_tactic test_simplify (True /\ True)
let _ = assert_by_tactic test_simplify (True \/ True)
let _ = assert_by_tactic test_simplify (True \/ False)
let _ = assert_by_tactic test_simplify (False \/ True)

let _ = assert_by_tactic test_simplify (False \/ (True /\ True))
let _ = assert_by_tactic test_simplify ((True /\ False) \/ (True /\ True))
let _ = assert_by_tactic test_simplify (False \/ ((True /\ False) \/ (True /\ True)))

let _ = assert_by_tactic test_simplify (False ==> True)
let _ = assert_by_tactic test_simplify (False ==> False)
let _ = assert_by_tactic test_simplify (True ==> True)

let _ = assert_by_tactic test_simplify ((False ==> False) ==> True)
let _ = assert_by_tactic test_simplify (False ==> (False ==> False))
let _ = assert_by_tactic test_simplify ((False ==> False) ==> (True ==> True))
let _ = assert_by_tactic test_simplify ((True ==> True) ==> (False ==> False))
