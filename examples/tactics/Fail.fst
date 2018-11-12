module Fail

// Making sure the unification engine respects failures

open FStar.Tactics

assume val p : Type
assume val q : Type
assume val r : Type

assume val f : squash p -> squash r
assume val g : squash q -> squash r

assume val vq : squash q

let tau () : Tac unit =
    let _ = trytac #unit (fun () -> apply (quote f); fail "oops wrong way") in
    apply (quote g);
    exact (quote vq)

let _ = assert_by_tactic r tau
