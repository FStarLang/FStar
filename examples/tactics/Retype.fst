module Retype

// Changing the type of a binder

open FStar.Tactics

assume val p : prop
assume val q : prop
assume val r : prop

assume val l : unit -> Lemma (p == r)
assume val l2 : unit -> Lemma (requires r) (ensures q)

let tau () : Tac unit =
    let _ = implies_intro () in
    let _ = implies_intro () in
    let _ = implies_intro () in
    let b = implies_intro () in

    binder_retype b; // call retype, get a goal `p == ?u`
    let pp = quote p in
    let rr = quote r in
    grewrite pp rr; // rewrite p to q, get `q == ?u`
    trefl (); // unify

    apply_lemma (quote l); //prove (p == q), asked by grewrite

    let e = cur_env () in
    match binders_of_env e with
    | [_;_;_;b] ->
        let t = type_of_binder b in
        let t = norm_term [] t in // contains uvar redexes.
        if FStar.Order.ne (compare_term t rr)
        then fail "binder was not retyped?"
        else ();

        apply_lemma (quote l2);
        assumption ();
        qed ()
    | _ ->
        fail "should be impossible"

let _ = 
    assert_by_tactic (True ==> True ==> True ==> p ==> q) tau
