module Clear

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

[@plugin]
let tau1 = fun () ->
                let _ = implies_intro () in
                clear_top ();
                let _ = implies_intro () in
                clear_top ();
                exact (`p)

let l1 (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi)) tau1


let clear_all_of_type (t : typ) : Tac unit =
    let e = cur_env () in
    let bs = binders_of_env e in
    let _ = map (fun b -> if term_eq (type_of_binder b) t
                          then clear b
                          else ())
         // We need to traverse the list backwards, to clear rightmost
         // binders first. Otherwise, if we go left-first, we will revert/intro
         // over a binder we want to clear and cause it to be refreshed.
         (List.rev bs) in
    ()

[@plugin]
let tau2 = fun () -> let e = cur_env () in
                       let n = List.length (binders_of_env e) in
                       let u = `int in
                       clear_all_of_type u;
                       let e = cur_env () in
                       // We're removing two binders
                       guard (List.length (binders_of_env e) = n - 2)

let l2 (x : int) (y : bool) (z : int) =
    assert_by_tactic (phi ==> (psi ==> xi)) tau2
