module FStar.Tactics.Arith

open FStar.Tactics
open FStar.Reflection
open FStar.Reflection.Arith
open FStar.List

// decide if the current goal is arith, drop the built representation of it
let is_arith_goal : tactic bool =
    eg <-- cur_goal;
    let (_, g), _ = eg in
    match run_tm (is_arith_prop g) with
    | Inr _ -> return true
    | Inl s -> return false

val split_arith : unit -> Tac unit
let rec split_arith = fun () -> (
    eg <-- cur_goal;
    let (_, g), _ = eg in
    b <-- is_arith_goal;
    if b then (
        prune "";;
        addns "Prims";;
        smt ()
    ) else (
        eg <-- cur_goal;
        let (_, g), _ = eg in
        match term_as_formula g with
        | True_ -> trivial
        | And l r -> seq FStar.Tactics.split split_arith
        | Implies p q -> (implies_intro;; seq split_arith revert)
        | Forall x p -> (bs <-- forall_intros; seq split_arith (revert_all bs))
        | _ ->
                return ()
    )) ()
