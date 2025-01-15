module FStarC.Syntax.CheckLN

open FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module L = FStarC.List

(* Computes the binding amount of a pattern.
Anywhere where this is defined already? *)
let rec pat_depth (p:pat) : int =
  match p.v with
  | Pat_constant _ -> 0
  | Pat_cons (p, _us_opt, ps) ->
     L.fold_left (fun d (p, _) -> d + pat_depth p) 0 ps
  | Pat_var _ -> 1
  | Pat_dot_term _ -> 0

(* Checks if, at most, n indices escape from a term *)
let rec is_ln' (n:int) (t:term) : bool =
  match (SS.compress t).n with
  | Tm_bvar bv -> bv.index < n

  | Tm_type _
  | Tm_name _
  | Tm_constant _
  | Tm_fvar _ -> true

  (* Should really be an fvar, but being conservative here *)
  | Tm_uinst (t, us) ->
    is_ln' n t &&
    is_ln'_univs n us

  | Tm_abs {bs;body;rc_opt} ->
    is_ln'_binders n bs &&
    is_ln' (n + L.length bs) body

  | Tm_arrow {bs;comp} ->
    is_ln'_binders n bs &&
    is_ln'_comp (n + L.length bs) comp

  | Tm_refine {b;phi} ->
    is_ln'_bv n b &&
    is_ln' (n+1) phi

  | Tm_app {hd; args} ->
    is_ln' n hd &&
    L.for_all (fun (t, aq) -> is_ln' n t) args

  | Tm_match {scrutinee; ret_opt; brs; rc_opt} ->
    is_ln' n scrutinee &&
    // TODO: check pats
    L.for_all (fun (p, _, t) -> is_ln' (n + pat_depth p) t) brs

  | Tm_ascribed {tm; asc; eff_opt} ->
    is_ln' n tm &&
    true // is_ln' n asc

  | Tm_let {lbs; body} ->
    is_ln'_letbindings n lbs &&
    is_ln' (n + L.length (snd lbs)) body

  | _ -> true

and is_ln'_letbindings (n:int) (lbs : letbindings) : bool =
  let isrec, lbs = lbs in
  L.for_all (fun lb -> is_ln'_letbinding n lb) lbs

and is_ln'_letbinding (n:int) (lb : letbinding) : bool =
  let {lbunivs; lbtyp; lbdef} = lb in
  let nu = List.length lbunivs in
  is_ln' (n+nu) lbtyp &&
  is_ln' (n+nu) lbdef

and is_ln'_binders (n:int) (bs : list binder) : bool =
  match bs with
  | [] -> true
  | b::bs ->
    is_ln'_binder n b && is_ln'_binders (n+1) bs

and is_ln'_binder (n:int) (b:binder) : bool =
  is_ln'_bv n b.binder_bv

and is_ln'_bv (n:int) (bv:bv) : bool =
  is_ln' n bv.sort

and is_ln'_comp (n:int) (c:comp) : bool =
  match c.n with
  | Total t -> is_ln' n t
  | GTotal t -> is_ln' n t
  | Comp ct -> is_ln'_comp_typ n ct

and is_ln'_comp_typ (n:nat) (ct:comp_typ) : bool =
  is_ln' n ct.result_typ &&
  L.for_all (fun (t,aq) -> is_ln' n t) ct.effect_args &&
//   L.for_all (is_ln' n) ct.flags
  true

and is_ln'_univ (n:nat) (u : universe) : bool =
  match SS.compress_univ u with
  | U_zero -> true
  | U_succ u -> is_ln'_univ n u
  | U_max us -> L.for_all (is_ln'_univ n) us
  | U_unif _ -> true // we're conservative with returning false since that would be an error
  | U_bvar i -> i < n
  | U_name _ -> true
  | U_unknown -> true

and is_ln'_univs (n:nat) (us : list universe) : bool =
  L.for_all (is_ln'_univ n) us

(* Checks if a term is locally nameless *)
let is_ln (t:term) : bool =
  is_ln' 0 t
