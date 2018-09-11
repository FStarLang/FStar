module FStar.Tactics.Arith

open FStar.Tactics
open FStar.Reflection.Formula
open FStar.Reflection.Arith

// decide if the current goal is arith, drop the built representation of it
let is_arith_goal () : Tac bool =
    let g = cur_goal () in
    match run_tm (is_arith_prop g) with
    | Inr _ -> true
    | _ -> false

val split_arith : unit -> Tac unit
let rec split_arith () =
    if is_arith_goal () then
        begin
        prune "";
        addns "Prims";
        smt ()
        end
    else begin
        let g = cur_goal () in
        match term_as_formula g with
        | True_ ->
            trivial ()
        | And l r ->
            seq FStar.Tactics.split split_arith
        | Implies p q ->
            let _ = implies_intro () in
            seq split_arith l_revert
        | Forall x p ->
            let bs = forall_intros () in
            seq split_arith (fun () -> l_revert_all bs)
        | _ ->
            ()
    end
