module Fail

// Making sure the unification engine respects failures

open FStar.Tactics

assume val p : Type
assume val q : Type
assume val r : Type

assume val f : squash p -> squash r
assume val g : squash q -> squash r

assume val vq : squash q

[@plugin]
let tau () : Tac unit =
    let _ = trytac #unit (fun () -> apply (`f); fail "oops wrong way") in
    apply (`g);
    exact (`vq)

let _ = assert_by_tactic r tau
