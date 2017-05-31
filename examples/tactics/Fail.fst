module Fail

// Making sure the unification engine respects failures

open FStar.Tactics

assume val p : Type
assume val q : Type
assume val r : Type

assume val f : squash p -> squash r
assume val g : squash q -> squash r

assume val vq : squash q

let tau : tactic unit =
    trytac #unit (dump "GG1";; apply (quote f);; dump "GG2";; fail "oops wrong way");;
    dump "GG 3";;
    apply (quote g);;
    exact (quote vq)

let _ = assert_by_tactic tau r
