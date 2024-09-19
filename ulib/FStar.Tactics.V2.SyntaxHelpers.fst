module FStar.Tactics.V2.SyntaxHelpers

open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.NamedView

(* These are fully-named variants of functions found in FStar.Reflection *)

private
let rec collect_arr' (bs : list binder) (c : comp) : Tac (list binder & comp) =
    begin match c with
    | C_Total t ->
        begin match inspect t with
        | Tv_Arrow b c ->
            collect_arr' (b::bs) c
        | _ ->
            (bs, c)
        end
    | _ -> (bs, c)
    end

let collect_arr_bs t =
    let (bs, c) = collect_arr' [] (C_Total t) in
    (List.Tot.Base.rev bs, c)

let collect_arr t =
    let (bs, c) = collect_arr' [] (C_Total t) in
    let ts = List.Tot.Base.map (fun (b:binder) -> b.sort) bs in
    (List.Tot.Base.rev ts, c)

private
let rec collect_abs' (bs : list binder) (t : term) : Tac (list binder & term) (decreases t) =
    match inspect t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

let collect_abs t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.Base.rev bs, t')

(* Copied from FStar.Tactics.V2.Derived *)
private
let fail (#a:Type) (m:string) = raise #a (TacticFailure (mkmsg m, None))

let rec mk_arr (bs: list binder) (cod : comp) : Tac term =
    match bs with
    | [] -> fail "mk_arr, empty binders"
    | [b] -> pack (Tv_Arrow b cod)
    | (b::bs) ->
      pack (Tv_Arrow b (C_Total (mk_arr bs cod)))

let rec mk_tot_arr (bs: list binder) (cod : term) : Tac term =
    match bs with
    | [] -> cod
    | (b::bs) ->
      pack (Tv_Arrow b (C_Total (mk_tot_arr bs cod)))

let lookup_lb (lbs:list letbinding) (nm:name) : Tac letbinding =
  let o = FStar.List.Tot.Base.find
             (fun lb -> (inspect_fv lb.lb_fv) = nm)
             lbs
  in
  match o with
  | Some lb -> lb
  | None -> fail "lookup_letbinding: Name not in let group"

let rec inspect_unascribe (t:term) : Tac (tv:term_view{notAscription tv}) =
  match inspect t with
  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ ->
    inspect_unascribe t
  | tv -> tv

(* Helpers for dealing with nested applications and arrows *)
let rec collect_app' (args : list argv) (t : term)
  : Tac (term & list argv) =
    match inspect_unascribe t with
    | Tv_App l r ->
        collect_app' (r::args) l
    | _ -> (t, args)

let collect_app = collect_app' []

(* Destruct an application into [h]ead fv, [u]niverses, and [a]rguments. *)
let hua (t:term) : Tac (option (fv & universes & list argv)) =
  let hd, args = collect_app t in
  match inspect hd with
  | Tv_FVar fv -> Some (fv, [], args)
  | Tv_UInst fv us -> Some (fv, us, args)
  | _ -> None
