module FStar.Tactics.SyntaxHelpers

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Types

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
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t [])) in
    (List.Tot.Base.rev bs, c)

val collect_arr : typ -> Tac (list typ * comp)
let collect_arr t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t [])) in
    let ts = List.Tot.Base.map type_of_binder bs in
    (List.Tot.Base.rev ts, c)

private
let rec collect_abs' (bs : list binder) (t : term) : Tac (list binder * term) (decreases t) =
    match inspect t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs : term -> Tac (list binder * term)
let collect_abs t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.Base.rev bs, t')

(* Copied from FStar.Tactics.Derived *)
private
let fail (#a:Type) (m:string) = raise #a (TacticFailure m)

let rec mk_arr (bs: list binder) (cod : comp) : Tac term =
    match bs with
    | [] -> fail "mk_arr, empty binders"
    | [b] -> pack (Tv_Arrow b cod)
    | (b::bs) -> pack (Tv_Arrow b (pack_comp (C_Total (mk_arr bs cod) [])))

let rec mk_tot_arr (bs: list binder) (cod : term) : Tac term =
    match bs with
    | [] -> cod
    | (b::bs) -> pack (Tv_Arrow b (pack_comp (C_Total (mk_tot_arr bs cod) [])))

let lookup_lb_view (lbs:list letbinding) (nm:name) : Tac lb_view =
  let o = FStar.List.Tot.Base.find
             (fun lb ->
              let lbv = inspect_lb lb in
              (inspect_fv lbv.lb_fv) = nm)
             lbs
  in
  match o with
  | Some lb -> inspect_lb lb
  | None -> fail "lookup_lb_view: Name not in let group"
