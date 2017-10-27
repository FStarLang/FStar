module FStar.Tactics.Arith

open FStar.Tactics
open FStar.Reflection.Formula
open FStar.Reflection.Arith

// decide if the current goal is arith, drop the built representation of it
let is_arith_goal : tactic bool =
    g <-- cur_goal;
    match run_tm (is_arith_prop g) with
    | Inr _ -> return true
    | Inl s -> return false

val split_arith : unit -> Tac unit
let rec split_arith = fun () -> (
    g <-- cur_goal;
    b <-- is_arith_goal;
    if b then (
        prune "";;
        addns "Prims";;
        smt
    ) else (
        g <-- cur_goal;
        match term_as_formula g with
        | True_ -> trivial
        | And l r -> seq FStar.Tactics.split split_arith
        | Implies p q -> (implies_intro;; seq split_arith l_revert)
        | Forall x p -> (bs <-- forall_intros; seq split_arith (l_revert_all bs))
        | _ ->
                return ()
    )) ()
