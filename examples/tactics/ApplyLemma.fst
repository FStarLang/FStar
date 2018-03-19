module ApplyLemma

open FStar.Tactics

assume val p : Type0
assume val q : Type0
assume val x : p

assume val lem1 : p -> Lemma q
assume val lem2 : p -> squash q

let _ = assert_by_tactic q
            (fun () -> apply_lemma (`lem1);
                       exact (`x))

let _ = assert_by_tactic q
            (fun () -> apply_lemma (`lem2);
                       exact (`x))
