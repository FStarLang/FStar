module FailFlow

open FStar.Tactics

let fail_flow () : Tac unit =
    fail "failing";
    assert False

(* This fails to typecheck, since the assert is definitely reachable *)
[@expect_failure]
let print_test () : Tac unit =
    print "not failing";
    assert False

(* None of these succeed (as in: return Success within the monad) *)
[@expect_failure]
let s_fail_flow () : TacS unit =
    fail "failing";
    assert False

[@expect_failure]
let s_print_test () : TacS unit =
    print "not failing";
    assert False
