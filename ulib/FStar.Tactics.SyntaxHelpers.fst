module FStar.Tactics.SyntaxHelpers

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

(* These are fully-named variants of functions found in FStar.Reflection *)

private
let rec collect_arr' (bs : list binder) (c : comp) : Tac (list binder * comp) =
    begin match inspect_comp c with
    | C_Total t _ ->
        begin match inspect t with
        | Tv_Arrow b c ->
            collect_arr' (b::bs) c
        | _ ->
            (bs, c)
        end
    | _ -> (bs, c)
    end

val collect_arr_bs : typ -> Tac (list binder * comp)
let collect_arr_bs t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t None)) in
    (List.Tot.rev bs, c)

val collect_arr : typ -> Tac (list typ * comp)
let collect_arr t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t None)) in
    let ts = List.Tot.map type_of_binder bs in
    (List.Tot.rev ts, c)

private
let rec collect_abs' (bs : list binder) (t : term) : Tac (list binder * term) (decreases t) =
    match inspect t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs : term -> Tac (list binder * term)
let collect_abs t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.rev bs, t')

let rec mk_tot_arr (bs: list binder) (cod : term) : Tac term =
    match bs with
    | [] -> cod
    | (b::bs) -> pack (Tv_Arrow b (pack_comp (C_Total (mk_tot_arr bs cod) None)))
