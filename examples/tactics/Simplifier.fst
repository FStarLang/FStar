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

let _ = assert_by_tactic (True /\ True)
                         test_simplify
let _ = assert_by_tactic (True \/ True)
                         test_simplify
let _ = assert_by_tactic (True \/ False)
                         test_simplify
let _ = assert_by_tactic (False \/ True)
                         test_simplify

let _ = assert_by_tactic (False \/ (True /\ True))
                         test_simplify
let _ = assert_by_tactic ((True /\ False) \/ (True /\ True))
                         test_simplify
let _ = assert_by_tactic (False \/ ((True /\ False) \/ (True /\ True)))
                         test_simplify

let _ = assert_by_tactic (False ==> True)
                         test_simplify
let _ = assert_by_tactic (False ==> False)
                         test_simplify
let _ = assert_by_tactic (True ==> True)
                         test_simplify

let _ = assert_by_tactic ((False ==> False) ==> True)
                         test_simplify
let _ = assert_by_tactic (False ==> (False ==> False))
                         test_simplify
let _ = assert_by_tactic ((False ==> False) ==> (True ==> True))
                         test_simplify
let _ = assert_by_tactic ((True ==> True) ==> (False ==> False))
                         test_simplify

let _ = assert_by_tactic (~False)
                         test_simplify
let _ = assert_by_tactic (~(~True))
                         test_simplify

let _ = assert_by_tactic (forall (x:int). True)
                         test_simplify
let _ = assert_by_tactic (forall (x:int). ((True ==> True) ==> (False ==> False)))
                         test_simplify

let _ = assert_by_tactic ((exists (x:int). False) ==> False)
                         test_simplify
let _ = assert_by_tactic (~(exists (x:int). False))
                         test_simplify
let _ = assert_by_tactic (~(exists (x:int). ((True ==> True) ==> (True ==> False))))
                         test_simplify

let _ = assert_by_tactic (False <==> False)
                         test_simplify
let _ = assert_by_tactic ((False <==> False) <==> True)
                         test_simplify
let _ = assert_by_tactic (False <==> (False <==> True))
                         test_simplify

let _ = assert_by_tactic ((exists (x:int). True) <==> True)
                         test_simplify
let _ = assert_by_tactic ((forall (x:int). False) <==> False)
                         test_simplify
