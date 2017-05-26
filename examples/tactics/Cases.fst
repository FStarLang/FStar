module C

open FStar.Tactics

assume val p : Type0
assume val q : Type0
assume val r : Type0

assume val f : p -> Lemma r
assume val g : q -> Lemma r

let test_cases (h : p \/ q) : Lemma r =
    assert_by_tactic
        (dump "GG 1";;
         t <-- quote h;
         cases t;;
         dump "GG 2";;
         fail "")
         r
