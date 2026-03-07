module FStarC.Syntax.CheckLN

open FStarC.Effect
open FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module L = FStarC.List

(* Computes the binding amount of a pattern.
Anywhere where this is defined already? *)
let rec pat_depth (p:pat) : ML int =
  match p.v with
  | Pat_constant _ -> 0
  | Pat_cons (p, _us_opt, ps) ->
     L.fold_left (fun d (p, _) -> d + pat_depth p) 0 ps
  | Pat_var _ -> 1
  | Pat_dot_term _ -> 0

(* Checks if, at most, n indices escape from a term *)
let rec is_ln' (n:int) (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_bvar bv -> bv.index < n

  | Tm_type _
  | Tm_name _
  | Tm_constant _
  | Tm_fvar _ -> true

  (* Should really be an fvar, but being conservative here *)
  | Tm_uinst (t, us) ->
    let r1 = is_ln' n t in
    let r2 = is_ln'_univs n us in
    r1 && r2

  | Tm_abs {bs;body;rc_opt} ->
    let r1 = is_ln'_binders n bs in
    let nbs = L.length bs in
    let r2 = is_ln' (n + nbs) body in
    r1 && r2

  | Tm_arrow {bs;comp} ->
    let r1 = is_ln'_binders n bs in
    let nbs = L.length bs in
    let r2 = is_ln'_comp (n + nbs) comp in
    r1 && r2

  | Tm_refine {b;phi} ->
    let r1 = is_ln'_bv n b in
    let r2 = is_ln' (n+1) phi in
    r1 && r2

  | Tm_app {hd; args} ->
    let r1 = is_ln' n hd in
    let r2 = L.for_all (fun (t, aq) -> is_ln' n t) args in
    r1 && r2

  | Tm_match {scrutinee; ret_opt; brs; rc_opt} ->
    let r1 = is_ln' n scrutinee in
    // TODO: check pats
    let r2 = L.for_all (fun (p, _, t) -> let d = pat_depth p in is_ln' (n + d) t) brs in
    r1 && r2

  | Tm_ascribed {tm; asc; eff_opt} ->
    let r1 = is_ln' n tm in
    r1 && true // is_ln' n asc

  | Tm_let {lbs; body} ->
    let r1 = is_ln'_letbindings n lbs in
    let nlbs = L.length (snd lbs) in
    let r2 = is_ln' (n + nlbs) body in
    r1 && r2

  | _ -> true

and is_ln'_letbindings (n:int) (lbs : letbindings) : ML bool =
  let isrec, lbs = lbs in
  L.for_all (fun lb -> is_ln'_letbinding n lb) lbs

and is_ln'_letbinding (n:int) (lb : letbinding) : ML bool =
  let {lbunivs; lbtyp; lbdef} = lb in
  let nu = List.length lbunivs in
  let r1 = is_ln' (n+nu) lbtyp in
  let r2 = is_ln' (n+nu) lbdef in
  r1 && r2

and is_ln'_binders (n:int) (bs : list binder) : ML bool =
  match bs with
  | [] -> true
  | b::bs ->
    let r1 = is_ln'_binder n b in
    let r2 = is_ln'_binders (n+1) bs in
    r1 && r2

and is_ln'_binder (n:int) (b:binder) : ML bool =
  is_ln'_bv n b.binder_bv

and is_ln'_bv (n:int) (bv:bv) : ML bool =
  is_ln' n bv.sort

and is_ln'_comp (n:int) (c:comp) : ML bool =
  match c.n with
  | Total t -> is_ln' n t
  | GTotal t -> is_ln' n t
  | Comp ct -> is_ln'_comp_typ n ct

and is_ln'_comp_typ (n:nat) (ct:comp_typ) : ML bool =
  let r1 = is_ln' n ct.result_typ in
  let r2 = L.for_all (fun (t,aq) -> is_ln' n t) ct.effect_args in
  r1 && r2 &&
//   L.for_all (is_ln' n) ct.flags
  true

and is_ln'_univ (n:nat) (u : universe) : ML bool =
  match SS.compress_univ u with
  | U_zero -> true
  | U_succ u -> is_ln'_univ n u
  | U_max us -> L.for_all (is_ln'_univ n) us
  | U_unif _ -> true // we're conservative with returning false since that would be an error
  | U_bvar i -> i < n
  | U_name _ -> true
  | U_unknown -> true

and is_ln'_univs (n:nat) (us : list universe) : ML bool =
  L.for_all (is_ln'_univ n) us

(* Checks if a term is locally nameless *)
let is_ln (t:term) : ML bool =
  is_ln' 0 t
