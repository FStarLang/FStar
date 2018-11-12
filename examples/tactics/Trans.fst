module Trans

open FStar.Tactics

assume val t : Type0
assume val a : t
assume val b : t

val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
let trans #a #x #z #y e1 e2 = ()

// Even if we admit the goals, an uninstantiated variable remains
[@expect_failure]
let _ = assert_by_tactic (a == b) (fun () -> (); apply_lemma (`trans); tadmit(); tadmit ())
