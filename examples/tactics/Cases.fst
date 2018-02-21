module Cases

(* *)

open FStar.Tactics
open FStar.Mul

assume val p : Type0
assume val q : Type0
assume val r : Type0

assume val f : unit -> Lemma (p ==> r)
assume val g : unit -> Lemma (q ==> r)

let test_cases (h : p \/ q) : Lemma r =
    assert_by_tactic r
        (t <-- quote h;
         cases_or t;;
         apply_lemma (quote f);;
         apply_lemma (quote g);;
         qed)

// Taking a squashed hypothesis, we can unsquash it as we're in an irrelevant context
let test_cases_unsquash (h : squash (p \/ q)) : Lemma r =
    assert_by_tactic r
        (t <-- quote h;
         t <-- unsquash t;
         cases_or t;;
         apply_lemma (quote f);;
         apply_lemma (quote g);;
         qed)

(* assume val pp : Type0 *)
(* assume val qq : Type0 *)
(* assume val ff :  pp -> Lemma qq *)
(* assume val gg : ~pp -> Lemma qq *)

(* let ll () : Lemma (pp \/ ~pp) = () *)

(* let test_em () : Lemma qq = *)
(*     assert_by_tactic qq *)
(*                      (empp <-- quote ll; *)
(*                       p_or_not_p <-- get_lemma empp; *)
(*                       p_or_not_p <-- unsquash p_or_not_p; *)
(*                       h_pp_npp <-- cases p_or_not_p; *)
(*                       let h_pp, h_npp = h_pp_npp in *)
(*                       apply_lemma (quote ff);; exact (return h_pp);; *)
(*                       apply_lemma (quote gg);; exact (return h_npp);; *)
(*                       qed *)
(*                      ) *)

assume val pred : bool -> Type
assume val pred_true  : squash (pred true)
assume val pred_false : squash (pred false)

let test_cases_bool (b:bool) : Lemma (pred b) =
    assert_by_tactic (pred b)
        (b <-- quote b;
         cases_bool b;;
         exact (quote pred_true);;
         exact (quote pred_false);;
         qed)

let test_cases_bool_2 (x:int) : Lemma (x + x == 2 * x) =
    assert_by_tactic (x + x == 2 * x)
        (t <-- quote (x = 0);
         cases_bool t)
