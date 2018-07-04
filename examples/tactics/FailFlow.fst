module FailFlow

open FStar.Tactics

let fail_flow () : Tac unit =
    fail "failing";
    assert False

let fail_flow' () : Tac unit =
    fail_act "failing";
    assert False

(* This fails to typecheck, since the assert is definitely reachable *)
[@Pervasives.fail]
let print_test () : Tac unit =
    print "not failing";
    assert False

(* Metaprograms that succeed *)
effect TacS (a:Type) = TAC a (fun _ p -> forall x ps. p (FStar.Tactics.Result.Success x ps))

(* None of these succeed (as in: return Success within the monad) *)
[@Pervasives.fail]
let s_fail_flow () : TacS unit =
    fail "failing";
    assert False

[@Pervasives.fail]
let s_fail_flow' () : TacS unit =
    fail_act "failing";
    assert False

[@Pervasives.fail]
let s_print_test () : TacS unit =
    print "not failing";
    assert False
