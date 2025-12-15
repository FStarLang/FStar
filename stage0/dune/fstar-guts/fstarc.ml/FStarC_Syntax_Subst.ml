open Prims
let rec apply_until_some :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> ('a Prims.list * 'b) FStar_Pervasives_Native.option
  =
  fun f s ->
    match s with
    | [] -> FStar_Pervasives_Native.None
    | s0::rest ->
        let uu___ = f s0 in
        (match uu___ with
         | FStar_Pervasives_Native.None -> apply_until_some f rest
         | FStar_Pervasives_Native.Some st ->
             FStar_Pervasives_Native.Some (rest, st))
let map_some_curry (f : 'a -> 'b -> 'c) (x : 'c)
  (uu___ : ('a * 'b) FStar_Pervasives_Native.option) : 'c=
  match uu___ with
  | FStar_Pervasives_Native.None -> x
  | FStar_Pervasives_Native.Some (a1, b1) -> f a1 b1
let apply_until_some_then_map (f : 'a -> 'b FStar_Pervasives_Native.option)
  (s : 'a Prims.list) (g : 'a Prims.list -> 'b -> 'c) (t : 'c) : 'c=
  let uu___ = apply_until_some f s in
  let uu___1 = map_some_curry g t in uu___1 uu___
let compose_subst (s1 : FStarC_Syntax_Syntax.subst_ts)
  (s2 : FStarC_Syntax_Syntax.subst_ts) : FStarC_Syntax_Syntax.subst_ts=
  let s =
    FStarC_List.op_At (FStar_Pervasives_Native.fst s1)
      (FStar_Pervasives_Native.fst s2) in
  let ropt =
    match FStar_Pervasives_Native.snd s2 with
    | FStarC_Syntax_Syntax.SomeUseRange uu___ ->
        FStar_Pervasives_Native.snd s2
    | uu___ -> FStar_Pervasives_Native.snd s1 in
  (s, ropt)
let delay (t : FStarC_Syntax_Syntax.term) (s : FStarC_Syntax_Syntax.subst_ts)
  : FStarC_Syntax_Syntax.term=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed
      { FStarC_Syntax_Syntax.tm1 = t'; FStarC_Syntax_Syntax.substs = s';_} ->
      let uu___ = let uu___1 = compose_subst s' s in (t', uu___1) in
      FStarC_Syntax_Syntax.mk_Tm_delayed uu___ t.FStarC_Syntax_Syntax.pos
  | uu___ ->
      FStarC_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStarC_Syntax_Syntax.pos
let rec force_uvar'
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax * Prims.bool)=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_uvar
      ({ FStarC_Syntax_Syntax.ctx_uvar_head = uv;
         FStarC_Syntax_Syntax.ctx_uvar_gamma = uu___;
         FStarC_Syntax_Syntax.ctx_uvar_binders = uu___1;
         FStarC_Syntax_Syntax.ctx_uvar_reason = uu___2;
         FStarC_Syntax_Syntax.ctx_uvar_range = uu___3;
         FStarC_Syntax_Syntax.ctx_uvar_meta = uu___4;_},
       s)
      ->
      let uu___5 = FStarC_Syntax_Unionfind.find uv in
      (match uu___5 with
       | FStar_Pervasives_Native.Some t' ->
           let uu___6 =
             let uu___7 = let uu___8 = delay t' s in force_uvar' uu___8 in
             FStar_Pervasives_Native.fst uu___7 in
           (uu___6, true)
       | uu___6 -> (t, false))
  | uu___ -> (t, false)
let force_uvar (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  let uu___ = force_uvar' t in
  match uu___ with
  | (t', forced) ->
      if forced
      then
        delay t'
          ([],
            (FStarC_Syntax_Syntax.SomeUseRange (t.FStarC_Syntax_Syntax.pos)))
      else t
let rec compress_univ (u : FStarC_Syntax_Syntax.universe) :
  FStarC_Syntax_Syntax.universe=
  match u with
  | FStarC_Syntax_Syntax.U_unif u' ->
      let uu___ = FStarC_Syntax_Unionfind.univ_find u' in
      (match uu___ with
       | FStar_Pervasives_Native.Some u1 -> compress_univ u1
       | uu___1 -> u)
  | uu___ -> u
let subst_bv (a : FStarC_Syntax_Syntax.bv)
  (s : FStarC_Syntax_Syntax.subst_elt Prims.list) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option=
  FStarC_Util.find_map s
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.DB (i, x) when i = a.FStarC_Syntax_Syntax.index
           ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Syntax_Syntax.range_of_bv a in
               FStarC_Syntax_Syntax.set_range_of_bv x uu___3 in
             FStarC_Syntax_Syntax.bv_to_name uu___2 in
           FStar_Pervasives_Native.Some uu___1
       | FStarC_Syntax_Syntax.DT (i, t) when i = a.FStarC_Syntax_Syntax.index
           -> FStar_Pervasives_Native.Some t
       | uu___1 -> FStar_Pervasives_Native.None)
let subst_nm (a : FStarC_Syntax_Syntax.bv)
  (s : FStarC_Syntax_Syntax.subst_elt Prims.list) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option=
  FStarC_Util.find_map s
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.NM (x, i) when FStarC_Syntax_Syntax.bv_eq a x
           ->
           let uu___1 =
             FStarC_Syntax_Syntax.bv_to_tm
               {
                 FStarC_Syntax_Syntax.ppname =
                   (a.FStarC_Syntax_Syntax.ppname);
                 FStarC_Syntax_Syntax.index = i;
                 FStarC_Syntax_Syntax.sort = (a.FStarC_Syntax_Syntax.sort)
               } in
           FStar_Pervasives_Native.Some uu___1
       | FStarC_Syntax_Syntax.NT (x, t) when FStarC_Syntax_Syntax.bv_eq a x
           -> FStar_Pervasives_Native.Some t
       | uu___1 -> FStar_Pervasives_Native.None)
let subst_univ_bv (x : Prims.int)
  (s : FStarC_Syntax_Syntax.subst_elt Prims.list) :
  FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option=
  FStarC_Util.find_map s
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.UN (y, t) when x = y ->
           FStar_Pervasives_Native.Some t
       | uu___1 -> FStar_Pervasives_Native.None)
let subst_univ_nm (x : FStarC_Syntax_Syntax.univ_name)
  (s : FStarC_Syntax_Syntax.subst_elt Prims.list) :
  FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option=
  FStarC_Util.find_map s
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.UD (y, i) when FStarC_Ident.ident_equals x y ->
           FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.U_bvar i)
       | uu___1 -> FStar_Pervasives_Native.None)
let rec subst_univ (s : FStarC_Syntax_Syntax.subst_elt Prims.list Prims.list)
  (u : FStarC_Syntax_Syntax.universe) : FStarC_Syntax_Syntax.universe=
  let u1 = compress_univ u in
  match u1 with
  | FStarC_Syntax_Syntax.U_bvar x ->
      apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
  | FStarC_Syntax_Syntax.U_name x ->
      apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
  | FStarC_Syntax_Syntax.U_zero -> u1
  | FStarC_Syntax_Syntax.U_unknown -> u1
  | FStarC_Syntax_Syntax.U_unif uu___ -> u1
  | FStarC_Syntax_Syntax.U_succ u2 ->
      let uu___ = subst_univ s u2 in FStarC_Syntax_Syntax.U_succ uu___
  | FStarC_Syntax_Syntax.U_max us ->
      let uu___ = FStarC_List.map (subst_univ s) us in
      FStarC_Syntax_Syntax.U_max uu___
let tag_with_range (t : FStarC_Syntax_Syntax.term)
  (s : FStarC_Syntax_Syntax.subst_ts) : FStarC_Syntax_Syntax.term=
  match FStar_Pervasives_Native.snd s with
  | FStarC_Syntax_Syntax.NoUseRange -> t
  | FStarC_Syntax_Syntax.SomeUseRange r ->
      let uu___ =
        let uu___1 = FStarC_Range_Type.use_range t.FStarC_Syntax_Syntax.pos in
        let uu___2 = FStarC_Range_Type.use_range r in
        FStarC_Range_Ops.rng_included uu___1 uu___2 in
      if uu___
      then t
      else
        (let r1 =
           let uu___2 = FStarC_Range_Type.use_range r in
           FStarC_Range_Type.set_use_range t.FStarC_Syntax_Syntax.pos uu___2 in
         let t' =
           match t.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_bvar bv ->
               let uu___2 =
                 FStarC_Class_HasRange.setPos
                   FStarC_Syntax_Syntax.hasRange_bv r1 bv in
               FStarC_Syntax_Syntax.Tm_bvar uu___2
           | FStarC_Syntax_Syntax.Tm_name bv ->
               let uu___2 =
                 FStarC_Class_HasRange.setPos
                   FStarC_Syntax_Syntax.hasRange_bv r1 bv in
               FStarC_Syntax_Syntax.Tm_name uu___2
           | FStarC_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 =
                 FStarC_Class_HasRange.setPos
                   FStarC_Syntax_Syntax.hasRange_fv r1 fv in
               FStarC_Syntax_Syntax.Tm_fvar uu___2
           | t'1 -> t'1 in
         {
           FStarC_Syntax_Syntax.n = t';
           FStarC_Syntax_Syntax.pos = r1;
           FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
           FStarC_Syntax_Syntax.hash_code =
             (t.FStarC_Syntax_Syntax.hash_code)
         })
let tag_lid_with_range (l : FStarC_Ident.lident)
  (s : ('uuuuu * FStarC_Syntax_Syntax.maybe_set_use_range)) :
  FStarC_Ident.lident=
  match FStar_Pervasives_Native.snd s with
  | FStarC_Syntax_Syntax.NoUseRange -> l
  | FStarC_Syntax_Syntax.SomeUseRange r ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Ident.range_of_lid l in
          FStarC_Range_Type.use_range uu___2 in
        let uu___2 = FStarC_Range_Type.use_range r in
        FStarC_Range_Ops.rng_included uu___1 uu___2 in
      if uu___
      then l
      else
        (let uu___2 =
           let uu___3 = FStarC_Ident.range_of_lid l in
           let uu___4 = FStarC_Range_Type.use_range r in
           FStarC_Range_Type.set_use_range uu___3 uu___4 in
         FStarC_Ident.set_lid_range l uu___2)
let mk_range (r : FStarC_Range_Type.range)
  (s : FStarC_Syntax_Syntax.subst_ts) : FStarC_Range_Type.range=
  match FStar_Pervasives_Native.snd s with
  | FStarC_Syntax_Syntax.NoUseRange -> r
  | FStarC_Syntax_Syntax.SomeUseRange r' ->
      let uu___ =
        let uu___1 = FStarC_Range_Type.use_range r in
        let uu___2 = FStarC_Range_Type.use_range r' in
        FStarC_Range_Ops.rng_included uu___1 uu___2 in
      if uu___
      then r
      else
        (let uu___2 = FStarC_Range_Type.use_range r' in
         FStarC_Range_Type.set_use_range r uu___2)
let rec subst' (s : FStarC_Syntax_Syntax.subst_ts)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let subst_tail tl = subst' (tl, (FStar_Pervasives_Native.snd s)) in
  match s with
  | ([], FStarC_Syntax_Syntax.NoUseRange) -> t
  | ([]::[], FStarC_Syntax_Syntax.NoUseRange) -> t
  | uu___ ->
      let t0 = t in
      (match t0.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_unknown -> tag_with_range t0 s
       | FStarC_Syntax_Syntax.Tm_constant uu___1 -> tag_with_range t0 s
       | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> tag_with_range t0 s
       | FStarC_Syntax_Syntax.Tm_delayed
           { FStarC_Syntax_Syntax.tm1 = t';
             FStarC_Syntax_Syntax.substs = s';_}
           ->
           let uu___1 = let uu___2 = compose_subst s' s in (t', uu___2) in
           FStarC_Syntax_Syntax.mk_Tm_delayed uu___1
             t.FStarC_Syntax_Syntax.pos
       | FStarC_Syntax_Syntax.Tm_bvar a ->
           apply_until_some_then_map (subst_bv a)
             (FStar_Pervasives_Native.fst s) subst_tail t0
       | FStarC_Syntax_Syntax.Tm_name a ->
           apply_until_some_then_map (subst_nm a)
             (FStar_Pervasives_Native.fst s) subst_tail t0
       | FStarC_Syntax_Syntax.Tm_type u ->
           let uu___1 =
             let uu___2 = subst_univ (FStar_Pervasives_Native.fst s) u in
             FStarC_Syntax_Syntax.Tm_type uu___2 in
           let uu___2 = mk_range t0.FStarC_Syntax_Syntax.pos s in
           FStarC_Syntax_Syntax.mk uu___1 uu___2
       | uu___1 ->
           let uu___2 = mk_range t.FStarC_Syntax_Syntax.pos s in
           FStarC_Syntax_Syntax.mk_Tm_delayed (t0, s) uu___2)
let subst_dec_order' (s : FStarC_Syntax_Syntax.subst_ts)
  (uu___ : FStarC_Syntax_Syntax.decreases_order) :
  FStarC_Syntax_Syntax.decreases_order=
  match uu___ with
  | FStarC_Syntax_Syntax.Decreases_lex l ->
      let uu___1 = FStarC_List.map (subst' s) l in
      FStarC_Syntax_Syntax.Decreases_lex uu___1
  | FStarC_Syntax_Syntax.Decreases_wf (rel, e) ->
      let uu___1 =
        let uu___2 = subst' s rel in
        let uu___3 = subst' s e in (uu___2, uu___3) in
      FStarC_Syntax_Syntax.Decreases_wf uu___1
let subst_flags' (s : FStarC_Syntax_Syntax.subst_ts)
  (flags : FStarC_Syntax_Syntax.cflag Prims.list) :
  FStarC_Syntax_Syntax.cflag Prims.list=
  FStarC_List.map
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.DECREASES dec_order ->
           let uu___1 = subst_dec_order' s dec_order in
           FStarC_Syntax_Syntax.DECREASES uu___1
       | f -> f) flags
let subst_bqual' (s : FStarC_Syntax_Syntax.subst_ts)
  (i : FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option)
  : FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option=
  match i with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
      let uu___ = let uu___1 = subst' s t in FStarC_Syntax_Syntax.Meta uu___1 in
      FStar_Pervasives_Native.Some uu___
  | uu___ -> i
let subst_aqual' (s : FStarC_Syntax_Syntax.subst_ts)
  (i : FStarC_Syntax_Syntax.aqual) : FStarC_Syntax_Syntax.aqual=
  match i with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some a ->
      let uu___ =
        let uu___1 =
          FStarC_List.map (subst' s) a.FStarC_Syntax_Syntax.aqual_attributes in
        {
          FStarC_Syntax_Syntax.aqual_implicit =
            (a.FStarC_Syntax_Syntax.aqual_implicit);
          FStarC_Syntax_Syntax.aqual_attributes = uu___1
        } in
      FStar_Pervasives_Native.Some uu___
let subst_comp_typ'
  (s :
    (FStarC_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStarC_Syntax_Syntax.maybe_set_use_range))
  (t : FStarC_Syntax_Syntax.comp_typ) : FStarC_Syntax_Syntax.comp_typ=
  match s with
  | ([], FStarC_Syntax_Syntax.NoUseRange) -> t
  | ([]::[], FStarC_Syntax_Syntax.NoUseRange) -> t
  | uu___ ->
      let uu___1 =
        FStarC_List.map (subst_univ (FStar_Pervasives_Native.fst s))
          t.FStarC_Syntax_Syntax.comp_univs in
      let uu___2 = tag_lid_with_range t.FStarC_Syntax_Syntax.effect_name s in
      let uu___3 = subst' s t.FStarC_Syntax_Syntax.result_typ in
      let uu___4 =
        FStarC_List.map
          (fun uu___5 ->
             match uu___5 with
             | (t1, imp) ->
                 let uu___6 = subst' s t1 in
                 let uu___7 = subst_aqual' s imp in (uu___6, uu___7))
          t.FStarC_Syntax_Syntax.effect_args in
      let uu___5 = subst_flags' s t.FStarC_Syntax_Syntax.flags in
      {
        FStarC_Syntax_Syntax.comp_univs = uu___1;
        FStarC_Syntax_Syntax.effect_name = uu___2;
        FStarC_Syntax_Syntax.result_typ = uu___3;
        FStarC_Syntax_Syntax.effect_args = uu___4;
        FStarC_Syntax_Syntax.flags = uu___5
      }
let subst_comp'
  (s :
    (FStarC_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStarC_Syntax_Syntax.maybe_set_use_range))
  (t : FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax=
  match s with
  | ([], FStarC_Syntax_Syntax.NoUseRange) -> t
  | ([]::[], FStarC_Syntax_Syntax.NoUseRange) -> t
  | uu___ ->
      (match t.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Total t1 ->
           let uu___1 = subst' s t1 in FStarC_Syntax_Syntax.mk_Total uu___1
       | FStarC_Syntax_Syntax.GTotal t1 ->
           let uu___1 = subst' s t1 in FStarC_Syntax_Syntax.mk_GTotal uu___1
       | FStarC_Syntax_Syntax.Comp ct ->
           let uu___1 = subst_comp_typ' s ct in
           FStarC_Syntax_Syntax.mk_Comp uu___1)
let subst_ascription' (s : FStarC_Syntax_Syntax.subst_ts)
  (asc : FStarC_Syntax_Syntax.ascription) :
  ((FStarC_Syntax_Syntax.term,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term
    FStar_Pervasives_Native.option * Prims.bool)=
  let uu___ = asc in
  match uu___ with
  | (annot, topt, use_eq) ->
      let annot1 =
        match annot with
        | FStar_Pervasives.Inl t ->
            let uu___1 = subst' s t in FStar_Pervasives.Inl uu___1
        | FStar_Pervasives.Inr c ->
            let uu___1 = subst_comp' s c in FStar_Pervasives.Inr uu___1 in
      let uu___1 = FStarC_Option.map (subst' s) topt in
      (annot1, uu___1, use_eq)
let shift (n : Prims.int) (s : FStarC_Syntax_Syntax.subst_elt) :
  FStarC_Syntax_Syntax.subst_elt=
  match s with
  | FStarC_Syntax_Syntax.DB (i, t) -> FStarC_Syntax_Syntax.DB ((i + n), t)
  | FStarC_Syntax_Syntax.DT (i, t) -> FStarC_Syntax_Syntax.DT ((i + n), t)
  | FStarC_Syntax_Syntax.UN (i, t) -> FStarC_Syntax_Syntax.UN ((i + n), t)
  | FStarC_Syntax_Syntax.NM (x, i) -> FStarC_Syntax_Syntax.NM (x, (i + n))
  | FStarC_Syntax_Syntax.UD (x, i) -> FStarC_Syntax_Syntax.UD (x, (i + n))
  | FStarC_Syntax_Syntax.NT uu___ -> s
let shift_subst (n : Prims.int) (s : FStarC_Syntax_Syntax.subst_t) :
  FStarC_Syntax_Syntax.subst_t= FStarC_List.map (shift n) s
let shift_subst' (n : Prims.int)
  (s : (FStarC_Syntax_Syntax.subst_t Prims.list * 'uuuuu)) :
  (FStarC_Syntax_Syntax.subst_t Prims.list * 'uuuuu)=
  let uu___ = FStarC_List.map (shift_subst n) (FStar_Pervasives_Native.fst s) in
  (uu___, (FStar_Pervasives_Native.snd s))
let subst_binder' (s : FStarC_Syntax_Syntax.subst_ts)
  (b : FStarC_Syntax_Syntax.binder) : FStarC_Syntax_Syntax.binder=
  let uu___ =
    let uu___1 = b.FStarC_Syntax_Syntax.binder_bv in
    let uu___2 =
      subst' s (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
    {
      FStarC_Syntax_Syntax.ppname = (uu___1.FStarC_Syntax_Syntax.ppname);
      FStarC_Syntax_Syntax.index = (uu___1.FStarC_Syntax_Syntax.index);
      FStarC_Syntax_Syntax.sort = uu___2
    } in
  let uu___1 = subst_bqual' s b.FStarC_Syntax_Syntax.binder_qual in
  let uu___2 = FStarC_List.map (subst' s) b.FStarC_Syntax_Syntax.binder_attrs in
  FStarC_Syntax_Syntax.mk_binder_with_attrs uu___ uu___1
    b.FStarC_Syntax_Syntax.binder_positivity uu___2
let subst_binder (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (b : FStarC_Syntax_Syntax.binder) : FStarC_Syntax_Syntax.binder=
  subst_binder' ([s], FStarC_Syntax_Syntax.NoUseRange) b
let subst_binders'
  (s :
    (FStarC_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStarC_Syntax_Syntax.maybe_set_use_range))
  (bs : FStarC_Syntax_Syntax.binder Prims.list) :
  FStarC_Syntax_Syntax.binder Prims.list=
  FStarC_List.mapi
    (fun i b ->
       if i = Prims.int_zero
       then subst_binder' s b
       else (let uu___1 = shift_subst' i s in subst_binder' uu___1 b)) bs
let subst_binders (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (bs : FStarC_Syntax_Syntax.binders) : FStarC_Syntax_Syntax.binders=
  subst_binders' ([s], FStarC_Syntax_Syntax.NoUseRange) bs
let subst_arg' (s : FStarC_Syntax_Syntax.subst_ts)
  (uu___ : (FStarC_Syntax_Syntax.term * 'uuuuu)) :
  (FStarC_Syntax_Syntax.term * 'uuuuu)=
  match uu___ with | (t, imp) -> let uu___1 = subst' s t in (uu___1, imp)
let subst_args' (s : FStarC_Syntax_Syntax.subst_ts) :
  (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list ->
    (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list=
  FStarC_List.map (subst_arg' s)
let subst_univs_opt
  (sub : FStarC_Syntax_Syntax.subst_elt Prims.list Prims.list)
  (us_opt :
    FStarC_Syntax_Syntax.universe Prims.list FStar_Pervasives_Native.option)
  : FStarC_Syntax_Syntax.universe Prims.list FStar_Pervasives_Native.option=
  match us_opt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some us ->
      let uu___ = FStarC_List.map (subst_univ sub) us in
      FStar_Pervasives_Native.Some uu___
let subst_pat'
  (s :
    (FStarC_Syntax_Syntax.subst_t Prims.list *
      FStarC_Syntax_Syntax.maybe_set_use_range))
  (p : FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t) :
  (FStarC_Syntax_Syntax.pat * Prims.int)=
  let rec aux n p1 =
    match p1.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_constant uu___ -> (p1, n)
    | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
        let us_opt1 =
          let uu___ =
            let uu___1 = shift_subst' n s in
            FStar_Pervasives_Native.fst uu___1 in
          subst_univs_opt uu___ us_opt in
        let uu___ =
          FStarC_List.fold_left
            (fun uu___1 uu___2 ->
               match (uu___1, uu___2) with
               | ((pats1, n1), (p2, imp)) ->
                   let uu___3 = aux n1 p2 in
                   (match uu___3 with | (p3, m) -> (((p3, imp) :: pats1), m)))
            ([], n) pats in
        (match uu___ with
         | (pats1, n1) ->
             ({
                FStarC_Syntax_Syntax.v =
                  (FStarC_Syntax_Syntax.Pat_cons
                     (fv, us_opt1, (FStarC_List.rev pats1)));
                FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
              }, n1))
    | FStarC_Syntax_Syntax.Pat_var x ->
        let s1 = shift_subst' n s in
        let x1 =
          let uu___ = subst' s1 x.FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (x.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (x.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___
          } in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_var x1);
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, (n + Prims.int_one))
    | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
        let s1 = shift_subst' n s in
        let eopt1 = FStarC_Option.map (subst' s1) eopt in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, n) in
  aux Prims.int_zero p
let push_subst_lcomp (s : FStarC_Syntax_Syntax.subst_ts)
  (lopt : FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  : FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option=
  match lopt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rc ->
      let residual_typ =
        FStarC_Option.map (subst' s) rc.FStarC_Syntax_Syntax.residual_typ in
      let rc1 =
        {
          FStarC_Syntax_Syntax.residual_effect =
            (rc.FStarC_Syntax_Syntax.residual_effect);
          FStarC_Syntax_Syntax.residual_typ = residual_typ;
          FStarC_Syntax_Syntax.residual_flags =
            (rc.FStarC_Syntax_Syntax.residual_flags)
        } in
      FStar_Pervasives_Native.Some rc1
let compose_uvar_subst (u : FStarC_Syntax_Syntax.ctx_uvar)
  (s0 : FStarC_Syntax_Syntax.subst_ts) (s : FStarC_Syntax_Syntax.subst_ts) :
  FStarC_Syntax_Syntax.subst_ts=
  let should_retain x =
    FStarC_Util.for_some
      (fun b -> FStarC_Syntax_Syntax.bv_eq x b.FStarC_Syntax_Syntax.binder_bv)
      u.FStarC_Syntax_Syntax.ctx_uvar_binders in
  let rec aux uu___ =
    match uu___ with
    | [] -> []
    | hd_subst::rest ->
        let hd =
          FStarC_List.collect
            (fun uu___1 ->
               match uu___1 with
               | FStarC_Syntax_Syntax.NT (x, t) ->
                   let uu___2 = should_retain x in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           delay t (rest, FStarC_Syntax_Syntax.NoUseRange) in
                         (x, uu___5) in
                       FStarC_Syntax_Syntax.NT uu___4 in
                     [uu___3]
                   else []
               | FStarC_Syntax_Syntax.NM (x, i) ->
                   let uu___2 = should_retain x in
                   if uu___2
                   then
                     let x_i =
                       FStarC_Syntax_Syntax.bv_to_tm
                         {
                           FStarC_Syntax_Syntax.ppname =
                             (x.FStarC_Syntax_Syntax.ppname);
                           FStarC_Syntax_Syntax.index = i;
                           FStarC_Syntax_Syntax.sort =
                             (x.FStarC_Syntax_Syntax.sort)
                         } in
                     let t =
                       subst' (rest, FStarC_Syntax_Syntax.NoUseRange) x_i in
                     (match t.FStarC_Syntax_Syntax.n with
                      | FStarC_Syntax_Syntax.Tm_bvar x_j ->
                          [FStarC_Syntax_Syntax.NM
                             (x, (x_j.FStarC_Syntax_Syntax.index))]
                      | uu___3 -> [FStarC_Syntax_Syntax.NT (x, t)])
                   else []
               | uu___2 -> []) hd_subst in
        let uu___1 = aux rest in FStarC_List.op_At hd uu___1 in
  let uu___ =
    aux
      (FStarC_List.op_At (FStar_Pervasives_Native.fst s0)
         (FStar_Pervasives_Native.fst s)) in
  match uu___ with
  | [] -> ([], (FStar_Pervasives_Native.snd s))
  | s' -> ([s'], (FStar_Pervasives_Native.snd s))
let rec push_subst_aux (resolve_uvars : Prims.bool)
  (s : FStarC_Syntax_Syntax.subst_ts)
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  let mk t' =
    let uu___ = mk_range t.FStarC_Syntax_Syntax.pos s in
    FStarC_Syntax_Syntax.mk t' uu___ in
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed uu___ ->
      failwith "Impossible (delayed node in push_subst)"
  | FStarC_Syntax_Syntax.Tm_lazy i ->
      (match i.FStarC_Syntax_Syntax.lkind with
       | FStarC_Syntax_Syntax.Lazy_embedding uu___ ->
           let t1 =
             let uu___1 =
               let uu___2 =
                 FStarC_Effect.op_Bang FStarC_Syntax_Syntax.lazy_chooser in
               FStarC_Option.must uu___2 in
             uu___1 i.FStarC_Syntax_Syntax.lkind i in
           push_subst_aux resolve_uvars s t1
       | uu___ -> tag_with_range t s)
  | FStarC_Syntax_Syntax.Tm_constant uu___ -> tag_with_range t s
  | FStarC_Syntax_Syntax.Tm_fvar uu___ -> tag_with_range t s
  | FStarC_Syntax_Syntax.Tm_unknown -> tag_with_range t s
  | FStarC_Syntax_Syntax.Tm_uvar (uv, s0) ->
      let fallback uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = compose_uvar_subst uv s0 s in (uv, uu___4) in
            FStarC_Syntax_Syntax.Tm_uvar uu___3 in
          {
            FStarC_Syntax_Syntax.n = uu___2;
            FStarC_Syntax_Syntax.pos = (t.FStarC_Syntax_Syntax.pos);
            FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (t.FStarC_Syntax_Syntax.hash_code)
          } in
        tag_with_range uu___1 s in
      if Prims.op_Negation resolve_uvars
      then fallback ()
      else
        (let uu___1 =
           FStarC_Syntax_Unionfind.find uv.FStarC_Syntax_Syntax.ctx_uvar_head in
         match uu___1 with
         | FStar_Pervasives_Native.None -> fallback ()
         | FStar_Pervasives_Native.Some t1 ->
             let uu___2 = compose_subst s0 s in
             push_subst_aux resolve_uvars uu___2 t1)
  | FStarC_Syntax_Syntax.Tm_type uu___ -> subst' s t
  | FStarC_Syntax_Syntax.Tm_bvar uu___ -> subst' s t
  | FStarC_Syntax_Syntax.Tm_name uu___ -> subst' s t
  | FStarC_Syntax_Syntax.Tm_uinst (t', us) ->
      let us1 =
        FStarC_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
      let uu___ = mk (FStarC_Syntax_Syntax.Tm_uinst (t', us1)) in
      tag_with_range uu___ s
  | FStarC_Syntax_Syntax.Tm_app
      { FStarC_Syntax_Syntax.hd = t0; FStarC_Syntax_Syntax.args = args;_} ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t0 in
          let uu___3 = subst_args' s args in
          {
            FStarC_Syntax_Syntax.hd = uu___2;
            FStarC_Syntax_Syntax.args = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_app uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t0; FStarC_Syntax_Syntax.asc = asc;
        FStarC_Syntax_Syntax.eff_opt = lopt;_}
      ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t0 in
          let uu___3 = subst_ascription' s asc in
          {
            FStarC_Syntax_Syntax.tm = uu___2;
            FStarC_Syntax_Syntax.asc = uu___3;
            FStarC_Syntax_Syntax.eff_opt = lopt
          } in
        FStarC_Syntax_Syntax.Tm_ascribed uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_abs
      { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = body;
        FStarC_Syntax_Syntax.rc_opt = lopt;_}
      ->
      let n = FStarC_List.length bs in
      let s' = shift_subst' n s in
      let uu___ =
        let uu___1 =
          let uu___2 = subst_binders' s bs in
          let uu___3 = subst' s' body in
          let uu___4 = push_subst_lcomp s' lopt in
          {
            FStarC_Syntax_Syntax.bs = uu___2;
            FStarC_Syntax_Syntax.body = uu___3;
            FStarC_Syntax_Syntax.rc_opt = uu___4
          } in
        FStarC_Syntax_Syntax.Tm_abs uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = comp;_} ->
      let n = FStarC_List.length bs in
      let uu___ =
        let uu___1 =
          let uu___2 = subst_binders' s bs in
          let uu___3 =
            let uu___4 = shift_subst' n s in subst_comp' uu___4 comp in
          {
            FStarC_Syntax_Syntax.bs1 = uu___2;
            FStarC_Syntax_Syntax.comp = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_arrow uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = phi;_} ->
      let x1 =
        let uu___ = subst' s x.FStarC_Syntax_Syntax.sort in
        {
          FStarC_Syntax_Syntax.ppname = (x.FStarC_Syntax_Syntax.ppname);
          FStarC_Syntax_Syntax.index = (x.FStarC_Syntax_Syntax.index);
          FStarC_Syntax_Syntax.sort = uu___
        } in
      let phi1 = let uu___ = shift_subst' Prims.int_one s in subst' uu___ phi in
      mk
        (FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b = x1; FStarC_Syntax_Syntax.phi = phi1 })
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = t0;
        FStarC_Syntax_Syntax.ret_opt = asc_opt;
        FStarC_Syntax_Syntax.brs = pats;
        FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
      ->
      let t01 = subst' s t0 in
      let pats1 =
        FStarC_List.map
          (fun uu___ ->
             match uu___ with
             | (pat, wopt, branch) ->
                 let uu___1 = subst_pat' s pat in
                 (match uu___1 with
                  | (pat1, n) ->
                      let s1 = shift_subst' n s in
                      let wopt1 =
                        match wopt with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some w ->
                            let uu___2 = subst' s1 w in
                            FStar_Pervasives_Native.Some uu___2 in
                      let branch1 = subst' s1 branch in
                      (pat1, wopt1, branch1))) pats in
      let asc_opt1 =
        match asc_opt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (b, asc) ->
            let b1 = subst_binder' s b in
            let asc1 =
              let uu___ = shift_subst' Prims.int_one s in
              subst_ascription' uu___ asc in
            FStar_Pervasives_Native.Some (b1, asc1) in
      let uu___ =
        let uu___1 =
          let uu___2 = push_subst_lcomp s lopt in
          {
            FStarC_Syntax_Syntax.scrutinee = t01;
            FStarC_Syntax_Syntax.ret_opt = asc_opt1;
            FStarC_Syntax_Syntax.brs = pats1;
            FStarC_Syntax_Syntax.rc_opt1 = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_match uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_let
      { FStarC_Syntax_Syntax.lbs = (is_rec, lbs);
        FStarC_Syntax_Syntax.body1 = body;_}
      ->
      let n = FStarC_List.length lbs in
      let sn = shift_subst' n s in
      let body1 = subst' sn body in
      let lbs1 =
        FStarC_List.map
          (fun lb ->
             let lbt = subst' s lb.FStarC_Syntax_Syntax.lbtyp in
             let lbd =
               if
                 is_rec &&
                   (FStar_Pervasives.uu___is_Inl
                      lb.FStarC_Syntax_Syntax.lbname)
               then subst' sn lb.FStarC_Syntax_Syntax.lbdef
               else subst' s lb.FStarC_Syntax_Syntax.lbdef in
             let lbname =
               match lb.FStarC_Syntax_Syntax.lbname with
               | FStar_Pervasives.Inl x ->
                   FStar_Pervasives.Inl
                     {
                       FStarC_Syntax_Syntax.ppname =
                         (x.FStarC_Syntax_Syntax.ppname);
                       FStarC_Syntax_Syntax.index =
                         (x.FStarC_Syntax_Syntax.index);
                       FStarC_Syntax_Syntax.sort = lbt
                     }
               | FStar_Pervasives.Inr fv -> FStar_Pervasives.Inr fv in
             let lbattrs =
               FStarC_List.map (subst' s) lb.FStarC_Syntax_Syntax.lbattrs in
             {
               FStarC_Syntax_Syntax.lbname = lbname;
               FStarC_Syntax_Syntax.lbunivs =
                 (lb.FStarC_Syntax_Syntax.lbunivs);
               FStarC_Syntax_Syntax.lbtyp = lbt;
               FStarC_Syntax_Syntax.lbeff = (lb.FStarC_Syntax_Syntax.lbeff);
               FStarC_Syntax_Syntax.lbdef = lbd;
               FStarC_Syntax_Syntax.lbattrs = lbattrs;
               FStarC_Syntax_Syntax.lbpos = (lb.FStarC_Syntax_Syntax.lbpos)
             }) lbs in
      mk
        (FStarC_Syntax_Syntax.Tm_let
           {
             FStarC_Syntax_Syntax.lbs = (is_rec, lbs1);
             FStarC_Syntax_Syntax.body1 = body1
           })
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t0;
        FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
          (bs, ps);_}
      ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t0 in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (subst' s) bs in
              let uu___6 = FStarC_List.map (subst_args' s) ps in
              (uu___5, uu___6) in
            FStarC_Syntax_Syntax.Meta_pattern uu___4 in
          {
            FStarC_Syntax_Syntax.tm2 = uu___2;
            FStarC_Syntax_Syntax.meta = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_meta uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t0;
        FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic (m, t1);_}
      ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t0 in
          let uu___3 =
            let uu___4 = let uu___5 = subst' s t1 in (m, uu___5) in
            FStarC_Syntax_Syntax.Meta_monadic uu___4 in
          {
            FStarC_Syntax_Syntax.tm2 = uu___2;
            FStarC_Syntax_Syntax.meta = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_meta uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t0;
        FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic_lift
          (m1, m2, t1);_}
      ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t0 in
          let uu___3 =
            let uu___4 = let uu___5 = subst' s t1 in (m1, m2, uu___5) in
            FStarC_Syntax_Syntax.Meta_monadic_lift uu___4 in
          {
            FStarC_Syntax_Syntax.tm2 = uu___2;
            FStarC_Syntax_Syntax.meta = uu___3
          } in
        FStarC_Syntax_Syntax.Tm_meta uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_quoted (tm, qi) ->
      (match qi.FStarC_Syntax_Syntax.qkind with
       | FStarC_Syntax_Syntax.Quote_dynamic ->
           let uu___ =
             let uu___1 = let uu___2 = subst' s tm in (uu___2, qi) in
             FStarC_Syntax_Syntax.Tm_quoted uu___1 in
           mk uu___
       | FStarC_Syntax_Syntax.Quote_static ->
           let qi1 = FStarC_Syntax_Syntax.on_antiquoted (subst' s) qi in
           mk (FStarC_Syntax_Syntax.Tm_quoted (tm, qi1)))
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = m;_} ->
      let uu___ =
        let uu___1 =
          let uu___2 = subst' s t1 in
          { FStarC_Syntax_Syntax.tm2 = uu___2; FStarC_Syntax_Syntax.meta = m
          } in
        FStarC_Syntax_Syntax.Tm_meta uu___1 in
      mk uu___
let push_subst (s : FStarC_Syntax_Syntax.subst_ts)
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  push_subst_aux true s t
let compress_subst (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed
      { FStarC_Syntax_Syntax.tm1 = t1; FStarC_Syntax_Syntax.substs = s;_} ->
      let resolve_uvars = false in push_subst_aux resolve_uvars s t1
  | uu___ -> t
let rec compress_slow (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  let t1 = force_uvar t in
  match t1.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed
      { FStarC_Syntax_Syntax.tm1 = t'; FStarC_Syntax_Syntax.substs = s;_} ->
      let uu___ = push_subst s t' in compress uu___
  | uu___ -> t1
and compress (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_delayed uu___ -> let r = compress_slow t in r
  | FStarC_Syntax_Syntax.Tm_uvar uu___ -> let r = compress_slow t in r
  | uu___ -> t
let subst (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  subst' ([s], FStarC_Syntax_Syntax.NoUseRange) t
let set_use_range (r : FStarC_Range_Type.range)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Range_Type.use_range r in
        FStarC_Range_Type.set_def_range r uu___3 in
      FStarC_Syntax_Syntax.SomeUseRange uu___2 in
    ([], uu___1) in
  subst' uu___ t
let subst_comp (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (t : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.comp=
  subst_comp' ([s], FStarC_Syntax_Syntax.NoUseRange) t
let subst_bqual (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (imp : FStarC_Syntax_Syntax.bqual) : FStarC_Syntax_Syntax.bqual=
  subst_bqual' ([s], FStarC_Syntax_Syntax.NoUseRange) imp
let subst_aqual (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (imp : FStarC_Syntax_Syntax.aqual) : FStarC_Syntax_Syntax.aqual=
  subst_aqual' ([s], FStarC_Syntax_Syntax.NoUseRange) imp
let subst_ascription (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (asc : FStarC_Syntax_Syntax.ascription) : FStarC_Syntax_Syntax.ascription=
  subst_ascription' ([s], FStarC_Syntax_Syntax.NoUseRange) asc
let subst_decreasing_order (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (dec : FStarC_Syntax_Syntax.decreases_order) :
  FStarC_Syntax_Syntax.decreases_order=
  subst_dec_order' ([s], FStarC_Syntax_Syntax.NoUseRange) dec
let subst_residual_comp (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (rc : FStarC_Syntax_Syntax.residual_comp) :
  FStarC_Syntax_Syntax.residual_comp=
  match rc.FStarC_Syntax_Syntax.residual_typ with
  | FStar_Pervasives_Native.None -> rc
  | FStar_Pervasives_Native.Some t ->
      let uu___ =
        let uu___1 = subst s t in FStar_Pervasives_Native.Some uu___1 in
      {
        FStarC_Syntax_Syntax.residual_effect =
          (rc.FStarC_Syntax_Syntax.residual_effect);
        FStarC_Syntax_Syntax.residual_typ = uu___;
        FStarC_Syntax_Syntax.residual_flags =
          (rc.FStarC_Syntax_Syntax.residual_flags)
      }
let closing_subst (bs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.subst_elt Prims.list=
  let uu___ =
    FStarC_List.fold_right
      (fun b uu___1 ->
         match uu___1 with
         | (subst1, n) ->
             (((FStarC_Syntax_Syntax.NM
                  ((b.FStarC_Syntax_Syntax.binder_bv), n)) :: subst1),
               (n + Prims.int_one))) bs ([], Prims.int_zero) in
  FStar_Pervasives_Native.fst uu___
let open_binders' (bs : FStarC_Syntax_Syntax.binders) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.subst_t)=
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | b::bs' ->
        let x' =
          let uu___ =
            FStarC_Syntax_Syntax.freshen_bv b.FStarC_Syntax_Syntax.binder_bv in
          let uu___1 =
            subst o
              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (uu___.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___1
          } in
        let imp = subst_bqual o b.FStarC_Syntax_Syntax.binder_qual in
        let attrs =
          FStarC_List.map (subst o) b.FStarC_Syntax_Syntax.binder_attrs in
        let o1 =
          let uu___ = shift_subst Prims.int_one o in
          (FStarC_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu___ in
        let uu___ = aux bs' o1 in
        (match uu___ with
         | (bs'1, o2) ->
             let uu___1 =
               let uu___2 =
                 FStarC_Syntax_Syntax.mk_binder_with_attrs x' imp
                   b.FStarC_Syntax_Syntax.binder_positivity attrs in
               uu___2 :: bs'1 in
             (uu___1, o2)) in
  aux bs []
let open_binders (bs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.binders=
  let uu___ = open_binders' bs in FStar_Pervasives_Native.fst uu___
let open_term' (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term *
    FStarC_Syntax_Syntax.subst_t)=
  let uu___ = open_binders' bs in
  match uu___ with
  | (bs', opening) -> let uu___1 = subst opening t in (bs', uu___1, opening)
let open_term (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term)=
  let uu___ = open_term' bs t in
  match uu___ with | (b, t1, uu___1) -> (b, t1)
let open_comp (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp)=
  let uu___ = open_binders' bs in
  match uu___ with
  | (bs', opening) -> let uu___1 = subst_comp opening t in (bs', uu___1)
let open_ascription (bs : FStarC_Syntax_Syntax.binders)
  (asc : FStarC_Syntax_Syntax.ascription) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.ascription)=
  let uu___ = open_binders' bs in
  match uu___ with
  | (bs', opening) ->
      let uu___1 = subst_ascription opening asc in (bs', uu___1)
let open_pat (p : FStarC_Syntax_Syntax.pat) :
  (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.subst_t)=
  let rec open_pat_aux sub p1 =
    match p1.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_constant uu___ -> (p1, sub)
    | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
        let us_opt1 = subst_univs_opt [sub] us_opt in
        let uu___ =
          FStarC_List.fold_left
            (fun uu___1 uu___2 ->
               match (uu___1, uu___2) with
               | ((pats1, sub1), (p2, imp)) ->
                   let uu___3 = open_pat_aux sub1 p2 in
                   (match uu___3 with
                    | (p3, sub2) -> (((p3, imp) :: pats1), sub2))) ([], sub)
            pats in
        (match uu___ with
         | (pats1, sub1) ->
             ({
                FStarC_Syntax_Syntax.v =
                  (FStarC_Syntax_Syntax.Pat_cons
                     (fv, us_opt1, (FStarC_List.rev pats1)));
                FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
              }, sub1))
    | FStarC_Syntax_Syntax.Pat_var x ->
        let x' =
          let uu___ = FStarC_Syntax_Syntax.freshen_bv x in
          let uu___1 = subst sub x.FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (uu___.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___1
          } in
        let sub1 =
          let uu___ = shift_subst Prims.int_one sub in
          (FStarC_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu___ in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_var x');
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, sub1)
    | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
        let eopt1 = FStarC_Option.map (subst sub) eopt in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, sub) in
  open_pat_aux [] p
let open_branch' (uu___ : FStarC_Syntax_Syntax.branch) :
  (FStarC_Syntax_Syntax.branch * FStarC_Syntax_Syntax.subst_t)=
  match uu___ with
  | (p, wopt, e) ->
      let uu___1 = open_pat p in
      (match uu___1 with
       | (p1, opening) ->
           let wopt1 =
             match wopt with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some w ->
                 let uu___2 = subst opening w in
                 FStar_Pervasives_Native.Some uu___2 in
           let e1 = subst opening e in ((p1, wopt1, e1), opening))
let open_branch (br : FStarC_Syntax_Syntax.branch) :
  FStarC_Syntax_Syntax.branch=
  let uu___ = open_branch' br in match uu___ with | (br1, uu___1) -> br1
let close (bs : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.term)
  : FStarC_Syntax_Syntax.term= let uu___ = closing_subst bs in subst uu___ t
let close_comp (bs : FStarC_Syntax_Syntax.binders)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.comp=
  let uu___ = closing_subst bs in subst_comp uu___ c
let close_binders (bs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.binders=
  let rec aux s bs1 =
    match bs1 with
    | [] -> []
    | b::tl ->
        let x =
          let uu___ = b.FStarC_Syntax_Syntax.binder_bv in
          let uu___1 =
            subst s
              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (uu___.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___1
          } in
        let imp = subst_bqual s b.FStarC_Syntax_Syntax.binder_qual in
        let attrs =
          FStarC_List.map (subst s) b.FStarC_Syntax_Syntax.binder_attrs in
        let s' =
          let uu___ = shift_subst Prims.int_one s in
          (FStarC_Syntax_Syntax.NM (x, Prims.int_zero)) :: uu___ in
        let uu___ =
          FStarC_Syntax_Syntax.mk_binder_with_attrs x imp
            b.FStarC_Syntax_Syntax.binder_positivity attrs in
        let uu___1 = aux s' tl in uu___ :: uu___1 in
  aux [] bs
let close_ascription (bs : FStarC_Syntax_Syntax.binders)
  (asc : FStarC_Syntax_Syntax.ascription) : FStarC_Syntax_Syntax.ascription=
  let uu___ = closing_subst bs in subst_ascription uu___ asc
let close_pat (p : FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t)
  :
  (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
    FStarC_Syntax_Syntax.subst_elt Prims.list)=
  let rec aux sub p1 =
    match p1.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_constant uu___ -> (p1, sub)
    | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
        let us_opt1 = subst_univs_opt [sub] us_opt in
        let uu___ =
          FStarC_List.fold_left
            (fun uu___1 uu___2 ->
               match (uu___1, uu___2) with
               | ((pats1, sub1), (p2, imp)) ->
                   let uu___3 = aux sub1 p2 in
                   (match uu___3 with
                    | (p3, sub2) -> (((p3, imp) :: pats1), sub2))) ([], sub)
            pats in
        (match uu___ with
         | (pats1, sub1) ->
             ({
                FStarC_Syntax_Syntax.v =
                  (FStarC_Syntax_Syntax.Pat_cons
                     (fv, us_opt1, (FStarC_List.rev pats1)));
                FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
              }, sub1))
    | FStarC_Syntax_Syntax.Pat_var x ->
        let x1 =
          let uu___ = subst sub x.FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (x.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (x.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___
          } in
        let sub1 =
          let uu___ = shift_subst Prims.int_one sub in
          (FStarC_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu___ in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_var x1);
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, sub1)
    | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
        let eopt1 = FStarC_Option.map (subst sub) eopt in
        ({
           FStarC_Syntax_Syntax.v = (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
           FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
         }, sub) in
  aux [] p
let close_branch (uu___ : FStarC_Syntax_Syntax.branch) :
  FStarC_Syntax_Syntax.branch=
  match uu___ with
  | (p, wopt, e) ->
      let uu___1 = close_pat p in
      (match uu___1 with
       | (p1, closing) ->
           let wopt1 =
             match wopt with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some w ->
                 let uu___2 = subst closing w in
                 FStar_Pervasives_Native.Some uu___2 in
           let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening (us : FStarC_Syntax_Syntax.univ_names) :
  (FStarC_Syntax_Syntax.subst_elt Prims.list * FStarC_Syntax_Syntax.univ_name
    Prims.list)=
  let n = (FStarC_List.length us) - Prims.int_one in
  let s =
    FStarC_List.mapi
      (fun i u ->
         FStarC_Syntax_Syntax.UN ((n - i), (FStarC_Syntax_Syntax.U_name u)))
      us in
  (s, us)
let univ_var_closing (us : FStarC_Syntax_Syntax.univ_names) :
  FStarC_Syntax_Syntax.subst_elt Prims.list=
  let n = (FStarC_List.length us) - Prims.int_one in
  FStarC_List.mapi (fun i u -> FStarC_Syntax_Syntax.UD (u, (n - i))) us
let open_univ_vars (us : FStarC_Syntax_Syntax.univ_names)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.term)=
  let uu___ = univ_var_opening us in
  match uu___ with | (s, us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp (us : FStarC_Syntax_Syntax.univ_names)
  (c : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.comp)=
  let uu___ = univ_var_opening us in
  match uu___ with | (s, us') -> let uu___1 = subst_comp s c in (us', uu___1)
let close_univ_vars (us : FStarC_Syntax_Syntax.univ_names)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let s = univ_var_closing us in subst s t
let close_univ_vars_comp (us : FStarC_Syntax_Syntax.univ_names)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.comp=
  let n = (FStarC_List.length us) - Prims.int_one in
  let s =
    FStarC_List.mapi (fun i u -> FStarC_Syntax_Syntax.UD (u, (n - i))) us in
  subst_comp s c
let open_let_rec (lbs : FStarC_Syntax_Syntax.letbinding Prims.list)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.letbinding Prims.list * FStarC_Syntax_Syntax.term)=
  let uu___ =
    let uu___1 = FStarC_Syntax_Syntax.is_top_level lbs in
    if uu___1
    then (Prims.int_zero, lbs, [])
    else
      FStarC_List.fold_right
        (fun lb uu___3 ->
           match uu___3 with
           | (i, lbs1, out) ->
               let x =
                 FStarC_Syntax_Syntax.freshen_bv
                   (FStar_Pervasives.__proj__Inl__item__v
                      lb.FStarC_Syntax_Syntax.lbname) in
               ((i + Prims.int_one),
                 ({
                    FStarC_Syntax_Syntax.lbname = (FStar_Pervasives.Inl x);
                    FStarC_Syntax_Syntax.lbunivs =
                      (lb.FStarC_Syntax_Syntax.lbunivs);
                    FStarC_Syntax_Syntax.lbtyp =
                      (lb.FStarC_Syntax_Syntax.lbtyp);
                    FStarC_Syntax_Syntax.lbeff =
                      (lb.FStarC_Syntax_Syntax.lbeff);
                    FStarC_Syntax_Syntax.lbdef =
                      (lb.FStarC_Syntax_Syntax.lbdef);
                    FStarC_Syntax_Syntax.lbattrs =
                      (lb.FStarC_Syntax_Syntax.lbattrs);
                    FStarC_Syntax_Syntax.lbpos =
                      (lb.FStarC_Syntax_Syntax.lbpos)
                  } :: lbs1), ((FStarC_Syntax_Syntax.DB (i, x)) :: out))) lbs
        (Prims.int_zero, [], []) in
  match uu___ with
  | (n_let_recs, lbs1, let_rec_opening) ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_List.hd lbs1 in
          uu___3.FStarC_Syntax_Syntax.lbunivs in
        FStarC_List.fold_right
          (fun u uu___3 ->
             match uu___3 with
             | (i, us, out) ->
                 let u1 =
                   FStarC_Syntax_Syntax.new_univ_name
                     FStar_Pervasives_Native.None in
                 ((i + Prims.int_one), (u1 :: us),
                   ((FStarC_Syntax_Syntax.UN
                       (i, (FStarC_Syntax_Syntax.U_name u1))) :: out)))
          uu___2 (n_let_recs, [], let_rec_opening) in
      (match uu___1 with
       | (uu___2, us, u_let_rec_opening) ->
           let lbs2 =
             FStarC_List.map
               (fun lb ->
                  let uu___3 =
                    subst u_let_rec_opening lb.FStarC_Syntax_Syntax.lbtyp in
                  let uu___4 =
                    subst u_let_rec_opening lb.FStarC_Syntax_Syntax.lbdef in
                  {
                    FStarC_Syntax_Syntax.lbname =
                      (lb.FStarC_Syntax_Syntax.lbname);
                    FStarC_Syntax_Syntax.lbunivs = us;
                    FStarC_Syntax_Syntax.lbtyp = uu___3;
                    FStarC_Syntax_Syntax.lbeff =
                      (lb.FStarC_Syntax_Syntax.lbeff);
                    FStarC_Syntax_Syntax.lbdef = uu___4;
                    FStarC_Syntax_Syntax.lbattrs =
                      (lb.FStarC_Syntax_Syntax.lbattrs);
                    FStarC_Syntax_Syntax.lbpos =
                      (lb.FStarC_Syntax_Syntax.lbpos)
                  }) lbs1 in
           let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec (lbs : FStarC_Syntax_Syntax.letbinding Prims.list)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.letbinding Prims.list * FStarC_Syntax_Syntax.term)=
  let uu___ =
    let uu___1 = FStarC_Syntax_Syntax.is_top_level lbs in
    if uu___1
    then (Prims.int_zero, [])
    else
      FStarC_List.fold_right
        (fun lb uu___3 ->
           match uu___3 with
           | (i, out) ->
               ((i + Prims.int_one),
                 ((FStarC_Syntax_Syntax.NM
                     ((FStar_Pervasives.__proj__Inl__item__v
                         lb.FStarC_Syntax_Syntax.lbname), i)) :: out))) lbs
        (Prims.int_zero, []) in
  match uu___ with
  | (n_let_recs, let_rec_closing) ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_List.hd lbs in
          uu___3.FStarC_Syntax_Syntax.lbunivs in
        FStarC_List.fold_right
          (fun u uu___3 ->
             match uu___3 with
             | (i, out) ->
                 ((i + Prims.int_one), ((FStarC_Syntax_Syntax.UD (u, i)) ::
                   out))) uu___2 (n_let_recs, let_rec_closing) in
      (match uu___1 with
       | (uu___2, u_let_rec_closing) ->
           let lbs1 =
             FStarC_List.map
               (fun lb ->
                  let uu___3 =
                    subst u_let_rec_closing lb.FStarC_Syntax_Syntax.lbtyp in
                  let uu___4 =
                    subst u_let_rec_closing lb.FStarC_Syntax_Syntax.lbdef in
                  {
                    FStarC_Syntax_Syntax.lbname =
                      (lb.FStarC_Syntax_Syntax.lbname);
                    FStarC_Syntax_Syntax.lbunivs =
                      (lb.FStarC_Syntax_Syntax.lbunivs);
                    FStarC_Syntax_Syntax.lbtyp = uu___3;
                    FStarC_Syntax_Syntax.lbeff =
                      (lb.FStarC_Syntax_Syntax.lbeff);
                    FStarC_Syntax_Syntax.lbdef = uu___4;
                    FStarC_Syntax_Syntax.lbattrs =
                      (lb.FStarC_Syntax_Syntax.lbattrs);
                    FStarC_Syntax_Syntax.lbpos =
                      (lb.FStarC_Syntax_Syntax.lbpos)
                  }) lbs in
           let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme (binders : FStarC_Syntax_Syntax.binders)
  (uu___ : FStarC_Syntax_Syntax.tscheme) : FStarC_Syntax_Syntax.tscheme=
  match uu___ with
  | (us, t) ->
      let n = (FStarC_List.length binders) - Prims.int_one in
      let k = FStarC_List.length us in
      let s =
        FStarC_List.mapi
          (fun i b ->
             FStarC_Syntax_Syntax.NM
               ((b.FStarC_Syntax_Syntax.binder_bv), (k + (n - i)))) binders in
      let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme (us : FStarC_Syntax_Syntax.univ_names)
  (uu___ : FStarC_Syntax_Syntax.tscheme) : FStarC_Syntax_Syntax.tscheme=
  match uu___ with
  | (us', t) ->
      let n = (FStarC_List.length us) - Prims.int_one in
      let k = FStarC_List.length us' in
      let s =
        FStarC_List.mapi
          (fun i x -> FStarC_Syntax_Syntax.UD (x, (k + (n - i)))) us in
      let uu___1 = subst s t in (us', uu___1)
let subst_tscheme (s : FStarC_Syntax_Syntax.subst_elt Prims.list)
  (uu___ : FStarC_Syntax_Syntax.tscheme) : FStarC_Syntax_Syntax.tscheme=
  match uu___ with
  | (us, t) ->
      let s1 = shift_subst (FStarC_List.length us) s in
      let uu___1 = subst s1 t in (us, uu___1)
let opening_of_binders (bs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.subst_t=
  let n = (FStarC_List.length bs) - Prims.int_one in
  FStarC_List.mapi
    (fun i b ->
       FStarC_Syntax_Syntax.DB ((n - i), (b.FStarC_Syntax_Syntax.binder_bv)))
    bs
let closing_of_binders (bs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.subst_t= closing_subst bs
let open_term_1 (b : FStarC_Syntax_Syntax.binder)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term)=
  let uu___ = open_term [b] t in
  match uu___ with
  | (b1::[], t1) -> (b1, t1)
  | uu___1 -> failwith "impossible: open_term_1"
let open_term_bvs (bvs : FStarC_Syntax_Syntax.bv Prims.list)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.bv Prims.list * FStarC_Syntax_Syntax.term)=
  let uu___ =
    let uu___1 = FStarC_List.map FStarC_Syntax_Syntax.mk_binder bvs in
    open_term uu___1 t in
  match uu___ with
  | (bs, t1) ->
      let uu___1 =
        FStarC_List.map (fun b -> b.FStarC_Syntax_Syntax.binder_bv) bs in
      (uu___1, t1)
let open_term_bv (bv : FStarC_Syntax_Syntax.bv)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term)=
  let uu___ = open_term_bvs [bv] t in
  match uu___ with
  | (bv1::[], t1) -> (bv1, t1)
  | uu___1 -> failwith "impossible: open_term_bv"
