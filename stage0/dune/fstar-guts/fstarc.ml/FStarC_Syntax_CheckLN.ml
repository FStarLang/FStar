open Prims
let rec pat_depth (p : FStarC_Syntax_Syntax.pat) : Prims.int=
  match p.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_constant uu___ -> Prims.int_zero
  | FStarC_Syntax_Syntax.Pat_cons (p1, _us_opt, ps) ->
      FStarC_List.fold_left
        (fun d uu___ ->
           match uu___ with
           | (p2, uu___1) -> let uu___2 = pat_depth p2 in d + uu___2)
        Prims.int_zero ps
  | FStarC_Syntax_Syntax.Pat_var uu___ -> Prims.int_one
  | FStarC_Syntax_Syntax.Pat_dot_term uu___ -> Prims.int_zero
let rec is_ln' (n : Prims.int) (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_bvar bv -> bv.FStarC_Syntax_Syntax.index < n
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_name uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_constant uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_uinst (t1, us) ->
      let uu___1 = is_ln' n t1 in if uu___1 then is_ln'_univs n us else false
  | FStarC_Syntax_Syntax.Tm_abs
      { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.body = body;
        FStarC_Syntax_Syntax.rc_opt = rc_opt;_}
      ->
      let uu___1 = is_ln'_binders n [b] in
      if uu___1 then is_ln' (n + Prims.int_one) body else false
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.b1 = b; FStarC_Syntax_Syntax.comp = comp;_} ->
      let uu___1 = is_ln'_binders n [b] in
      if uu___1 then is_ln'_comp (n + Prims.int_one) comp else false
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = b; FStarC_Syntax_Syntax.phi = phi;_} ->
      let uu___1 = is_ln'_bv n b in
      if uu___1 then is_ln' (n + Prims.int_one) phi else false
  | FStarC_Syntax_Syntax.Tm_app
      { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.arg = arg;_} ->
      let uu___1 = is_ln' n hd in
      if uu___1
      then let uu___2 = arg in (match uu___2 with | (t1, aq) -> is_ln' n t1)
      else false
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = scrutinee;
        FStarC_Syntax_Syntax.ret_opt = ret_opt;
        FStarC_Syntax_Syntax.brs = brs;
        FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
      ->
      let uu___1 = is_ln' n scrutinee in
      if uu___1
      then
        FStarC_List.for_all
          (fun uu___2 ->
             match uu___2 with
             | (p, uu___3, t1) ->
                 let uu___4 = let uu___5 = pat_depth p in n + uu___5 in
                 is_ln' uu___4 t1) brs
      else false
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = tm; FStarC_Syntax_Syntax.asc = asc;
        FStarC_Syntax_Syntax.eff_opt = eff_opt;_}
      -> let uu___1 = is_ln' n tm in if uu___1 then true else false
  | FStarC_Syntax_Syntax.Tm_let
      { FStarC_Syntax_Syntax.lbs = lbs; FStarC_Syntax_Syntax.body1 = body;_}
      ->
      let uu___1 = is_ln'_letbindings n lbs in
      if uu___1
      then
        is_ln' (n + (FStarC_List.length (FStar_Pervasives_Native.snd lbs)))
          body
      else false
  | uu___1 -> true
and is_ln'_letbindings (n : Prims.int)
  (lbs : FStarC_Syntax_Syntax.letbindings) : Prims.bool=
  let uu___ = lbs in
  match uu___ with
  | (isrec, lbs1) ->
      FStarC_List.for_all (fun lb -> is_ln'_letbinding n lb) lbs1
and is_ln'_letbinding (n : Prims.int) (lb : FStarC_Syntax_Syntax.letbinding)
  : Prims.bool=
  let uu___ = lb in
  match uu___ with
  | { FStarC_Syntax_Syntax.lbname = uu___1;
      FStarC_Syntax_Syntax.lbunivs = lbunivs;
      FStarC_Syntax_Syntax.lbtyp = lbtyp;
      FStarC_Syntax_Syntax.lbeff = uu___2;
      FStarC_Syntax_Syntax.lbdef = lbdef;
      FStarC_Syntax_Syntax.lbattrs = uu___3;
      FStarC_Syntax_Syntax.lbpos = uu___4;_} ->
      let nu = FStar_List_Tot_Base.length lbunivs in
      let uu___5 = is_ln' (n + nu) lbtyp in
      if uu___5 then is_ln' (n + nu) lbdef else false
and is_ln'_binders (n : Prims.int)
  (bs : FStarC_Syntax_Syntax.binder Prims.list) : Prims.bool=
  match bs with
  | [] -> true
  | b::bs1 ->
      let uu___ = is_ln'_binder n b in
      if uu___ then is_ln'_binders (n + Prims.int_one) bs1 else false
and is_ln'_binder (n : Prims.int) (b : FStarC_Syntax_Syntax.binder) :
  Prims.bool= is_ln'_bv n b.FStarC_Syntax_Syntax.binder_bv
and is_ln'_bv (n : Prims.int) (bv : FStarC_Syntax_Syntax.bv) : Prims.bool=
  is_ln' n bv.FStarC_Syntax_Syntax.sort
and is_ln'_comp (n : Prims.int) (c : FStarC_Syntax_Syntax.comp) : Prims.bool=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Comp ct -> is_ln'_comp_typ n ct
and is_ln'_comp_typ (n : Prims.nat) (ct : FStarC_Syntax_Syntax.comp_typ) :
  Prims.bool=
  let uu___ = is_ln' n ct.FStarC_Syntax_Syntax.result_typ in
  if uu___ then true else false
and is_ln'_univ (n : Prims.nat) (u : FStarC_Syntax_Syntax.universe) :
  Prims.bool=
  let uu___ = FStarC_Syntax_Subst.compress_univ u in
  match uu___ with
  | FStarC_Syntax_Syntax.U_zero -> true
  | FStarC_Syntax_Syntax.U_succ u1 -> is_ln'_univ n u1
  | FStarC_Syntax_Syntax.U_max us -> FStarC_List.for_all (is_ln'_univ n) us
  | FStarC_Syntax_Syntax.U_unif uu___1 -> true
  | FStarC_Syntax_Syntax.U_bvar i -> i < n
  | FStarC_Syntax_Syntax.U_name uu___1 -> true
  | FStarC_Syntax_Syntax.U_unknown -> true
and is_ln'_univs (n : Prims.nat)
  (us : FStarC_Syntax_Syntax.universe Prims.list) : Prims.bool=
  FStarC_List.for_all (is_ln'_univ n) us
let is_ln (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  is_ln' Prims.int_zero t
