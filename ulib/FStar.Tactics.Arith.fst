module FStar.Tactics.Arith

open FStar.Tactics
open FStar.Reflection.Arith
open FStar.List

// decide if the current goal is arith
let is_arith_goal : tactic bool =
    eg <-- cur_goal;
    let _, g = eg in
    match is_arith_prop g 0 with
    | Inr _ -> return true
    | Inl s -> return false

val split_arith : unit -> Tac unit
let rec split_arith = fun () -> (
    print "GGGG";;
    eg <-- cur_goal;
    let _, g = eg in
    b <-- is_arith_goal;
    print (term_to_string g ^ ": " ^ (if b then "is" else "is not") ^ " an arith goal");;
    if b then (
        prune "";;
        addns "Prims";;
        smt ()
    ) else (
        eg <-- cur_goal;
        let _, g = eg in
        match term_as_formula g with
        | True_ -> trivial
        | And l r -> seq FStar.Tactics.split split_arith
        | Implies p q -> (implies_intro;; seq split_arith revert)
        | Forall x p -> (bs <-- forall_intros; seq split_arith (revert_all bs))
        | _ ->
                return ()
    )) ()
