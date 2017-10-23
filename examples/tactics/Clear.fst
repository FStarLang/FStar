module Clear

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

let l1 (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi))
            (implies_intro;;
             clear_top;;
             implies_intro;;
             clear_top;;
             exact (quote p)
             )

let clear_all_of_type (t : typ) : tactic unit =
    e <-- cur_env;
    let bs = binders_of_env e in
    mapM (fun b -> if term_eq (type_of_binder b) t
                   then clear b
                   else idtac)
         // We need to traverse the list backwards, to clear rightmost
         // binders first. Otherwise, if we go left-first, we will revert/intro
         // over a binder we want to clear and cause it to be refreshed.
         (List.rev bs);;
    return ()

let l2 (x : int) (y : bool) (z : int) =
    assert_by_tactic (phi ==> (psi ==> xi))
            (e <-- cur_env;
             guard (List.length (binders_of_env e) = 3);;
             u <-- quote int;
             clear_all_of_type u;;
             e <-- cur_env;
             guard (List.length (binders_of_env e) = 1))
