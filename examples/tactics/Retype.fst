module Retype

// Changing the type of a binder

open FStar.Tactics

assume val p : prop
assume val q : prop
assume val r : prop

assume val l : unit -> Lemma (p == r)
assume val l2 : unit -> Lemma (requires r) (ensures q)

let assumption' : tactic unit =
    apply_raw (quote FStar.Squash.return_squash);;
    assumption

let tau : tactic unit =
    implies_intro;;
    implies_intro;;
    implies_intro;;
    b <-- implies_intro;

    binder_retype b;; // call retype, get a goal `p == ?u`
    pp <-- quote p;
    rr <-- quote r;
    grewrite pp rr;; // rewrite p to q, get `q == ?u`
    trefl;; // unify

    apply_lemma (quote l);; //prove (p == q), asked by grewrite

    e <-- cur_env;
    match binders_of_env e with
    | [_;_;_;b] ->
        let t = type_of_binder b in
        t <-- norm_term [] t; // contains uvar redexes.
        if FStar.Order.ne (compare_term t rr)
        then fail "binder was not retyped?"
        else idtac;;

        apply_lemma (quote l2);;
        assumption';;
        qed
    | _ ->
        fail "should be impossible"

let _ = 
    assert_by_tactic (True ==> True ==> True ==> p ==> q) tau
