module MApply

open FStar.Tactics

assume val p : Type0
assume val q : Type0
assume val x : squash p

assume val lem     : unit -> Lemma (requires p) (ensures q)
assume val lem_imp : unit -> Lemma (p ==> q)
assume val f_sq    : squash p -> squash q
assume val f_unsq  : squash p -> q

let _ =
    assert_by_tactic q (fun () -> mapply (quote lem_imp);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote lem);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote f_sq);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote f_unsq);
                                  mapply (quote x))
