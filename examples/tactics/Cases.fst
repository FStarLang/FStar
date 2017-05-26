module Cases

open FStar.Tactics

assume val p : Type0
assume val q : Type0
assume val r : Type0

assume val f : p -> Lemma r
assume val g : q -> Lemma r

let test_cases (h : p \/ q) : Lemma r =
    assert_by_tactic
        (t <-- quote h;
         h_pq <-- cases t;
         let h_p, h_q = h_pq in
         apply_lemma (quote f);;
         exact (return h_p);;
         apply_lemma (quote g);;
         exact (return h_q);;
         qed)
         r
