module Cases

(* *)

open FStar.Tactics
open FStar.Mul

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

// Taking a squashed hypothesis, we can un squash it as we're in an irrelevant context
let test_cases_unsquash (h : squash (p \/ q)) : Lemma r =
    assert_by_tactic
        (t <-- quote h;
         t <-- unsquash t;
         h_pq <-- cases t;
         let h_p, h_q = h_pq in
         apply_lemma (quote f);;
         exact (return h_p);;
         apply_lemma (quote g);;
         exact (return h_q);;
         qed)
         r

assume val pp : Type0
assume val qq : Type0
assume val ff :  pp -> Lemma qq
assume val gg : ~pp -> Lemma qq

let ll () : Lemma (pp \/ ~pp) = ()

let test_em () : Lemma qq =
    assert_by_tactic (empp <-- quote ll;
                      p_or_not_p <-- get_lemma empp;
                      p_or_not_p <-- unsquash p_or_not_p;
                      h_pp_npp <-- cases p_or_not_p;
                      let h_pp, h_npp = h_pp_npp in
                      apply_lemma (quote ff);; exact (return h_pp);;
                      apply_lemma (quote gg);; exact (return h_npp);;
                      qed
                     )
                     qq

assume val pred : bool -> Type
assume val pred_true  : pred true
assume val pred_false : pred false

let test_cases_bool (b:bool) : Lemma (pred b) =
    assert_by_tactic
        (dump "GG 1";;
         cases_bool b;;
         dump "GG 2";;
         exact (quote pred_true);;
         dump "GG 3";;
         exact (quote pred_false);;
         dump "GG 4";;
         qed)
        (pred b)

let test_cases_bool_2 (x:int) : Lemma (x + x == 2 * x) =
    assert_by_tactic
        (dump "BEFORE";;
         cases_bool (x = 0);;
         dump "AFTER") (x + x == 2 * x)
