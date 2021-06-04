open Prims
let subst_to_string :
  'uuuuu . (FStar_Syntax_Syntax.bv * 'uuuuu) Prims.list -> Prims.string =
  fun s ->
    let uu___ =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu___1 ->
              match uu___1 with
              | (b, uu___2) ->
                  FStar_Ident.string_of_id b.FStar_Syntax_Syntax.ppname)) in
    FStar_All.pipe_right uu___ (FStar_String.concat ", ")
let rec apply_until_some :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
      'uuuuu Prims.list ->
        ('uuuuu Prims.list * 'uuuuu1) FStar_Pervasives_Native.option
  =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu___ = f s0 in
          (match uu___ with
           | FStar_Pervasives_Native.None -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1 -> 'uuuuu2) ->
      'uuuuu2 -> ('uuuuu * 'uuuuu1) FStar_Pervasives_Native.option -> 'uuuuu2
  =
  fun f ->
    fun x ->
      fun uu___ ->
        match uu___ with
        | FStar_Pervasives_Native.None -> x
        | FStar_Pervasives_Native.Some (a, b) -> f a b
let apply_until_some_then_map :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
      'uuuuu Prims.list ->
        ('uuuuu Prims.list -> 'uuuuu1 -> 'uuuuu2) -> 'uuuuu2 -> 'uuuuu2
  =
  fun f ->
    fun s ->
      fun g ->
        fun t ->
          let uu___ = apply_until_some f s in
          FStar_All.pipe_right uu___ (map_some_curry g t)
let compose_subst :
  'uuuuu .
    ('uuuuu Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('uuuuu Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('uuuuu Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1 ->
    fun s2 ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu___ ->
            FStar_Pervasives_Native.snd s2
        | uu___ -> FStar_Pervasives_Native.snd s1 in
      (s, ropt)
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t ->
    fun s ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed (t', s') ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu___ ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu___;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu___1;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu___2;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu___3;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu___4;
           FStar_Syntax_Syntax.ctx_uvar_range = uu___5;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu___6;_},
         s)
        ->
        let uu___7 = FStar_Syntax_Unionfind.find uv in
        (match uu___7 with
         | FStar_Pervasives_Native.Some t' ->
             let uu___8 =
               let uu___9 = let uu___10 = delay t' s in force_uvar' uu___10 in
               FStar_Pervasives_Native.fst uu___9 in
             (uu___8, true)
         | uu___8 -> (t, false))
    | uu___ -> (t, false)
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu___ = force_uvar' t in
    match uu___ with
    | (t', forced) ->
        if forced
        then
          delay t'
            ([],
              (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos)))
        else t
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu___ = FStar_Syntax_Unionfind.univ_find u' in
        (match uu___ with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu___1 -> u)
    | uu___ -> u
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.DB (i, x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu___3 in
                 FStar_Syntax_Syntax.bv_to_name uu___2 in
               FStar_Pervasives_Native.Some uu___1
           | uu___1 -> FStar_Pervasives_Native.None)
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.NM (x, i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu___1 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___2 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___2.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___2.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu___1
           | FStar_Syntax_Syntax.NT (x, t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu___1 -> FStar_Pervasives_Native.None)
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.UN (y, t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu___1 -> FStar_Pervasives_Native.None)
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | FStar_Syntax_Syntax.UD (y, i) when FStar_Ident.ident_equals x y
               -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu___1 -> FStar_Pervasives_Native.None)
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s ->
    fun u ->
      let u1 = compress_univ u in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero -> u1
      | FStar_Syntax_Syntax.U_unknown -> u1
      | FStar_Syntax_Syntax.U_unif uu___ -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu___ = subst_univ s u2 in FStar_Syntax_Syntax.U_succ uu___
      | FStar_Syntax_Syntax.U_max us ->
          let uu___ = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu___
let tag_with_range :
  'uuuuu .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('uuuuu * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu___ =
            let uu___1 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos in
            let uu___2 = FStar_Range.use_range r in
            FStar_Range.rng_included uu___1 uu___2 in
          if uu___
          then t
          else
            (let r1 =
               let uu___2 = FStar_Range.use_range r in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu___2 in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu___2 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                   FStar_Syntax_Syntax.Tm_bvar uu___2
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu___2 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                   FStar_Syntax_Syntax.Tm_name uu___2
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   let v =
                     let uu___2 = fv.FStar_Syntax_Syntax.fv_name in
                     let uu___3 = FStar_Ident.set_lid_range l r1 in
                     {
                       FStar_Syntax_Syntax.v = uu___3;
                       FStar_Syntax_Syntax.p = (uu___2.FStar_Syntax_Syntax.p)
                     } in
                   let fv1 =
                     let uu___2 = fv in
                     {
                       FStar_Syntax_Syntax.fv_name = v;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___2.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___2.FStar_Syntax_Syntax.fv_qual)
                     } in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t'1 -> t'1 in
             let uu___2 = t in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars = (uu___2.FStar_Syntax_Syntax.vars)
             })
let tag_lid_with_range :
  'uuuuu .
    FStar_Ident.lident ->
      ('uuuuu * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Ident.range_of_lid l in
              FStar_Range.use_range uu___2 in
            let uu___2 = FStar_Range.use_range r in
            FStar_Range.rng_included uu___1 uu___2 in
          if uu___
          then l
          else
            (let uu___2 =
               let uu___3 = FStar_Ident.range_of_lid l in
               let uu___4 = FStar_Range.use_range r in
               FStar_Range.set_use_range uu___3 uu___4 in
             FStar_Ident.set_lid_range l uu___2)
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu___ =
            let uu___1 = FStar_Range.use_range r in
            let uu___2 = FStar_Range.use_range r' in
            FStar_Range.rng_included uu___1 uu___2 in
          if uu___
          then r
          else
            (let uu___2 = FStar_Range.use_range r' in
             FStar_Range.set_use_range r uu___2)
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun t ->
      let subst_tail tl = subst' (tl, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([], FStar_Syntax_Syntax.NoUseRange) -> t
      | ([]::[], FStar_Syntax_Syntax.NoUseRange) -> t
      | uu___ ->
          let t0 = t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu___1 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu___1 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (t', s') ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu___1 =
                 let uu___2 = subst_univ (FStar_Pervasives_Native.fst s) u in
                 FStar_Syntax_Syntax.Tm_type uu___2 in
               let uu___2 = mk_range t0.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk uu___1 uu___2
           | uu___1 ->
               let uu___2 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu___2)
let (subst_dec_order' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.decreases_order ->
      FStar_Syntax_Syntax.decreases_order)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Syntax_Syntax.Decreases_lex l ->
          let uu___1 = FStar_All.pipe_right l (FStar_List.map (subst' s)) in
          FStar_Syntax_Syntax.Decreases_lex uu___1
      | FStar_Syntax_Syntax.Decreases_wf (rel, e) ->
          let uu___1 =
            let uu___2 = subst' s rel in
            let uu___3 = subst' s e in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Decreases_wf uu___1
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s ->
    fun flags ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___ ->
              match uu___ with
              | FStar_Syntax_Syntax.DECREASES dec_order ->
                  let uu___1 = subst_dec_order' s dec_order in
                  FStar_Syntax_Syntax.DECREASES uu___1
              | f -> f))
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s ->
    fun i ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu___ =
            let uu___1 = subst' s t in FStar_Syntax_Syntax.Meta uu___1 in
          FStar_Pervasives_Native.Some uu___
      | uu___ -> i
let (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s ->
    fun t ->
      match s with
      | ([], FStar_Syntax_Syntax.NoUseRange) -> t
      | ([]::[], FStar_Syntax_Syntax.NoUseRange) -> t
      | uu___ ->
          let uu___1 = t in
          let uu___2 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu___3 = tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu___4 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu___5 =
            FStar_List.map
              (fun uu___6 ->
                 match uu___6 with
                 | (t1, imp) ->
                     let uu___7 = subst' s t1 in
                     let uu___8 = subst_imp' s imp in (uu___7, uu___8))
              t.FStar_Syntax_Syntax.effect_args in
          let uu___6 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu___2;
            FStar_Syntax_Syntax.effect_name = uu___3;
            FStar_Syntax_Syntax.result_typ = uu___4;
            FStar_Syntax_Syntax.effect_args = uu___5;
            FStar_Syntax_Syntax.flags = uu___6
          }
let (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun t ->
      match s with
      | ([], FStar_Syntax_Syntax.NoUseRange) -> t
      | ([]::[], FStar_Syntax_Syntax.NoUseRange) -> t
      | uu___ ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1, uopt) ->
               let uu___1 = subst' s t1 in
               let uu___2 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu___1 uu___2
           | FStar_Syntax_Syntax.GTotal (t1, uopt) ->
               let uu___1 = subst' s t1 in
               let uu___2 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu___1 uu___2
           | FStar_Syntax_Syntax.Comp ct ->
               let uu___1 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu___1)
let (subst_ascription' :
  FStar_Syntax_Syntax.subst_ts ->
    ((FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStar_Syntax_Syntax.term
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives.either * FStar_Syntax_Syntax.term
        FStar_Pervasives_Native.option))
  =
  fun s ->
    fun asc ->
      let uu___ = asc in
      match uu___ with
      | (annot, topt) ->
          let annot1 =
            match annot with
            | FStar_Pervasives.Inl t ->
                let uu___1 = subst' s t in FStar_Pervasives.Inl uu___1
            | FStar_Pervasives.Inr c ->
                let uu___1 = subst_comp' s c in FStar_Pervasives.Inr uu___1 in
          let uu___1 = FStar_Util.map_opt topt (subst' s) in (annot1, uu___1)
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n ->
    fun s ->
      match s with
      | FStar_Syntax_Syntax.DB (i, t) -> FStar_Syntax_Syntax.DB ((i + n), t)
      | FStar_Syntax_Syntax.UN (i, t) -> FStar_Syntax_Syntax.UN ((i + n), t)
      | FStar_Syntax_Syntax.NM (x, i) -> FStar_Syntax_Syntax.NM (x, (i + n))
      | FStar_Syntax_Syntax.UD (x, i) -> FStar_Syntax_Syntax.UD (x, (i + n))
      | FStar_Syntax_Syntax.NT uu___ -> s
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n -> fun s -> FStar_List.map (shift n) s
let shift_subst' :
  'uuuuu .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuu) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuu)
  =
  fun n ->
    fun s ->
      let uu___ =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n)) in
      (uu___, (FStar_Pervasives_Native.snd s))
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun s ->
    fun b ->
      let uu___ =
        let uu___1 = b.FStar_Syntax_Syntax.binder_bv in
        let uu___2 =
          subst' s (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname = (uu___1.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = (uu___1.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu___2
        } in
      let uu___1 = subst_imp' s b.FStar_Syntax_Syntax.binder_qual in
      let uu___2 =
        FStar_All.pipe_right b.FStar_Syntax_Syntax.binder_attrs
          (FStar_List.map (subst' s)) in
      FStar_Syntax_Syntax.mk_binder_with_attrs uu___ uu___1 uu___2
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.binder Prims.list)
  =
  fun s ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i ->
              fun b ->
                if i = Prims.int_zero
                then subst_binder' s b
                else
                  (let uu___1 = shift_subst' i s in subst_binder' uu___1 b)))
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s -> fun bs -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
let subst_arg' :
  'uuuuu .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuu) ->
        (FStar_Syntax_Syntax.term * 'uuuuu)
  =
  fun s ->
    fun uu___ ->
      match uu___ with | (t, imp) -> let uu___1 = subst' s t in (uu___1, imp)
let subst_args' :
  'uuuuu .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list
  = fun s -> FStar_List.map (subst_arg' s)
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s ->
    fun p ->
      let rec aux n p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu___ -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
            let uu___ =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu___1 ->
                      fun uu___2 ->
                        match (uu___1, uu___2) with
                        | ((pats1, n1), (p2, imp)) ->
                            let uu___3 = aux n1 p2 in
                            (match uu___3 with
                             | (p3, m) -> (((p3, imp) :: pats1), m))) 
                   ([], n)) in
            (match uu___ with
             | (pats1, n1) ->
                 ((let uu___1 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p = (uu___1.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___ = x in
              let uu___1 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu___1
              } in
            ((let uu___ = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___ = x in
              let uu___1 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu___1
              } in
            ((let uu___ = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___ = x in
              let uu___1 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu___1
              } in
            let t01 = subst' s1 t0 in
            ((let uu___ = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }), n) in
      aux Prims.int_zero p
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s ->
    fun lopt ->
      match lopt with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu___ =
            let uu___1 = rc in
            let uu___2 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu___2;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu___
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u ->
    fun s0 ->
      fun s ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun b ->
                  FStar_Syntax_Syntax.bv_eq x b.FStar_Syntax_Syntax.binder_bv)) in
        let rec aux uu___ =
          match uu___ with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Syntax_Syntax.NT (x, t) ->
                            let uu___2 = should_retain x in
                            if uu___2
                            then
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange) in
                                  (x, uu___5) in
                                FStar_Syntax_Syntax.NT uu___4 in
                              [uu___3]
                            else []
                        | FStar_Syntax_Syntax.NM (x, i) ->
                            let uu___2 = should_retain x in
                            if uu___2
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___3 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___3.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___3.FStar_Syntax_Syntax.sort)
                                   }) in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu___3 -> [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu___2 -> [])) in
              let uu___1 = aux rest in FStar_List.append hd uu___1 in
        let uu___ =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s)) in
        match uu___ with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun t ->
      let mk t' =
        let uu___ = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' uu___ in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu___ ->
               let t1 =
                 let uu___1 =
                   let uu___2 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                   FStar_Util.must uu___2 in
                 uu___1 i.FStar_Syntax_Syntax.lkind i in
               push_subst s t1
           | uu___ -> tag_with_range t s)
      | FStar_Syntax_Syntax.Tm_constant uu___ -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu___ -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv, s0) ->
          let uu___ =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head in
          (match uu___ with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 = t in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = compose_uvar_subst uv s0 s in (uv, uu___5) in
                   FStar_Syntax_Syntax.Tm_uvar uu___4 in
                 {
                   FStar_Syntax_Syntax.n = uu___3;
                   FStar_Syntax_Syntax.pos = (uu___2.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___2.FStar_Syntax_Syntax.vars)
                 } in
               tag_with_range uu___1 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu___ -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu___ -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu___ = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1)) in
          tag_with_range uu___ s
      | FStar_Syntax_Syntax.Tm_app (t0, args) ->
          let uu___ =
            let uu___1 =
              let uu___2 = subst' s t0 in
              let uu___3 = subst_args' s args in (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_app uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_ascribed (t0, asc, lopt) ->
          let uu___ =
            let uu___1 =
              let uu___2 = subst' s t0 in
              let uu___3 = subst_ascription' s asc in (uu___2, uu___3, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
          let n = FStar_List.length bs in
          let s' = shift_subst' n s in
          let uu___ =
            let uu___1 =
              let uu___2 = subst_binders' s bs in
              let uu___3 = subst' s' body in
              let uu___4 = push_subst_lcomp s' lopt in
              (uu___2, uu___3, uu___4) in
            FStar_Syntax_Syntax.Tm_abs uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
          let n = FStar_List.length bs in
          let uu___ =
            let uu___1 =
              let uu___2 = subst_binders' s bs in
              let uu___3 =
                let uu___4 = shift_subst' n s in subst_comp' uu___4 comp in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_arrow uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let x1 =
            let uu___ = x in
            let uu___1 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let phi1 =
            let uu___ = shift_subst' Prims.int_one s in subst' uu___ phi in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0, asc_opt, pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
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
                             (pat1, wopt1, branch1)))) in
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Util.map_opt asc_opt (subst_ascription' s) in
              (t01, uu___2, pats1) in
            FStar_Syntax_Syntax.Tm_match uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) ->
          let n = FStar_List.length lbs in
          let sn = shift_subst' n s in
          let body1 = subst' sn body in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp in
                    let lbd =
                      let uu___ =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu___
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Pervasives.Inl x ->
                          FStar_Pervasives.Inl
                            (let uu___ = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Pervasives.Inr fv -> FStar_Pervasives.Inr fv in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs in
                    let uu___ = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___.FStar_Syntax_Syntax.lbpos)
                    })) in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_pattern (bs, ps)) ->
          let uu___ =
            let uu___1 =
              let uu___2 = subst' s t0 in
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_List.map (subst' s) bs in
                  let uu___6 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                  (uu___5, uu___6) in
                FStar_Syntax_Syntax.Meta_pattern uu___4 in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) ->
          let uu___ =
            let uu___1 =
              let uu___2 = subst' s t0 in
              let uu___3 =
                let uu___4 = let uu___5 = subst' s t1 in (m, uu___5) in
                FStar_Syntax_Syntax.Meta_monadic uu___4 in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) ->
          let uu___ =
            let uu___1 =
              let uu___2 = subst' s t0 in
              let uu___3 =
                let uu___4 = let uu___5 = subst' s t1 in (m1, m2, uu___5) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu___4 in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic ->
               let uu___ =
                 let uu___1 = let uu___2 = subst' s tm in (uu___2, qi) in
                 FStar_Syntax_Syntax.Tm_quoted uu___1 in
               mk uu___
           | FStar_Syntax_Syntax.Quote_static ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let uu___ =
            let uu___1 = let uu___2 = subst' s t1 in (uu___2, m) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let t1 = force_uvar t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t', s) ->
        let uu___ = push_subst s t' in compress uu___
    | uu___ -> t1
and (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu___, uu___1) ->
        let r = compress_slow t in r
    | FStar_Syntax_Syntax.Tm_uvar (uu___, uu___1) ->
        let r = compress_slow t in r
    | uu___ -> t
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun t -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu___3 in
          FStar_Syntax_Syntax.SomeUseRange uu___2 in
        ([], uu___1) in
      subst' uu___ t
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s -> fun t -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  = fun s -> fun imp -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp
let (subst_ascription :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.ascription -> FStar_Syntax_Syntax.ascription)
  =
  fun s ->
    fun asc -> subst_ascription' ([s], FStar_Syntax_Syntax.NoUseRange) asc
let (subst_decreasing_order :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.decreases_order ->
      FStar_Syntax_Syntax.decreases_order)
  =
  fun s ->
    fun dec -> subst_dec_order' ([s], FStar_Syntax_Syntax.NoUseRange) dec
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs ->
    let uu___ =
      FStar_List.fold_right
        (fun b ->
           fun uu___1 ->
             match uu___1 with
             | (subst1, n) ->
                 (((FStar_Syntax_Syntax.NM
                      ((b.FStar_Syntax_Syntax.binder_bv), n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero) in
    FStar_All.pipe_right uu___ FStar_Pervasives_Native.fst
let (open_binders' :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.subst_t))
  =
  fun bs ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | b::bs' ->
          let x' =
            let uu___ =
              FStar_Syntax_Syntax.freshen_bv b.FStar_Syntax_Syntax.binder_bv in
            let uu___1 =
              subst o
                (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let imp = subst_imp o b.FStar_Syntax_Syntax.binder_qual in
          let attrs =
            FStar_All.pipe_right b.FStar_Syntax_Syntax.binder_attrs
              (FStar_List.map (subst o)) in
          let o1 =
            let uu___ = shift_subst Prims.int_one o in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu___ in
          let uu___ = aux bs' o1 in
          (match uu___ with
           | (bs'1, o2) ->
               let uu___1 =
                 let uu___2 =
                   FStar_Syntax_Syntax.mk_binder_with_attrs x' imp attrs in
                 uu___2 :: bs'1 in
               (uu___1, o2)) in
    aux bs []
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs -> let uu___ = open_binders' bs in FStar_Pervasives_Native.fst uu___
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs ->
    fun t ->
      let uu___ = open_binders' bs in
      match uu___ with
      | (bs', opening) ->
          let uu___1 = subst opening t in (bs', uu___1, opening)
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let uu___ = open_term' bs t in
      match uu___ with | (b, t1, uu___1) -> (b, t1)
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs ->
    fun t ->
      let uu___ = open_binders' bs in
      match uu___ with
      | (bs', opening) -> let uu___1 = subst_comp opening t in (bs', uu___1)
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu___ -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu___ =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu___1 ->
                    fun uu___2 ->
                      match (uu___1, uu___2) with
                      | ((pats1, sub1), (p2, imp)) ->
                          let uu___3 = open_pat_aux sub1 p2 in
                          (match uu___3 with
                           | (p3, sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub)) in
          (match uu___ with
           | (pats1, sub1) ->
               ((let uu___1 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p = (uu___1.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___ = FStar_Syntax_Syntax.freshen_bv x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let sub1 =
            let uu___ = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu___ in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___ = FStar_Syntax_Syntax.freshen_bv x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let sub1 =
            let uu___ = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu___ in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___ = x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let t01 = subst sub t0 in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub) in
    open_pat_aux [] p
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu___ ->
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
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br ->
    let uu___ = open_branch' br in match uu___ with | (br1, uu___1) -> br1
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun bs -> fun t -> let uu___ = closing_subst bs in subst uu___ t
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun bs -> fun c -> let uu___ = closing_subst bs in subst_comp uu___ c
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | b::tl ->
          let x =
            let uu___ = b.FStar_Syntax_Syntax.binder_bv in
            let uu___1 =
              subst s
                (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let imp = subst_imp s b.FStar_Syntax_Syntax.binder_qual in
          let attrs =
            FStar_All.pipe_right b.FStar_Syntax_Syntax.binder_attrs
              (FStar_List.map (subst s)) in
          let s' =
            let uu___ = shift_subst Prims.int_one s in
            (FStar_Syntax_Syntax.NM (x, Prims.int_zero)) :: uu___ in
          let uu___ = FStar_Syntax_Syntax.mk_binder_with_attrs x imp attrs in
          let uu___1 = aux s' tl in uu___ :: uu___1 in
    aux [] bs
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p ->
    let rec aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu___ -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu___ =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu___1 ->
                    fun uu___2 ->
                      match (uu___1, uu___2) with
                      | ((pats1, sub1), (p2, imp)) ->
                          let uu___3 = aux sub1 p2 in
                          (match uu___3 with
                           | (p3, sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub)) in
          (match uu___ with
           | (pats1, sub1) ->
               ((let uu___1 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p = (uu___1.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___ = x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let sub1 =
            let uu___ = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu___ in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___ = x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let sub1 =
            let uu___ = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu___ in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___ = x in
            let uu___1 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let t01 = subst sub t0 in
          ((let uu___ = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
            }), sub) in
    aux [] p
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu___ ->
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
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us ->
    let n = (FStar_List.length us) - Prims.int_one in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i ->
              fun u ->
                FStar_Syntax_Syntax.UN
                  ((n - i), (FStar_Syntax_Syntax.U_name u)))) in
    (s, us)
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us ->
    let n = (FStar_List.length us) - Prims.int_one in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i -> fun u -> FStar_Syntax_Syntax.UD (u, (n - i))))
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us ->
    fun t ->
      let uu___ = univ_var_opening us in
      match uu___ with | (s, us') -> let t1 = subst s t in (us', t1)
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us ->
    fun c ->
      let uu___ = univ_var_opening us in
      match uu___ with
      | (s, us') -> let uu___1 = subst_comp s c in (us', uu___1)
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us -> fun t -> let s = univ_var_closing us in subst s t
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us ->
    fun c ->
      let n = (FStar_List.length us) - Prims.int_one in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i -> fun u -> FStar_Syntax_Syntax.UD (u, (n - i)))) in
      subst_comp s c
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu___1
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu___3 ->
                 match uu___3 with
                 | (i, lbs1, out) ->
                     let x =
                       let uu___4 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu___4 in
                     ((i + Prims.int_one),
                       ((let uu___4 = lb in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (FStar_Pervasives.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___4.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___4.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___4.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___4.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___4.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___4.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], []) in
      match uu___ with
      | (n_let_recs, lbs1, let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb ->
                    let uu___1 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu___2 ->
                             match uu___2 with
                             | (i, us, out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + Prims.int_one), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu___1 with
                    | (uu___2, us, u_let_rec_opening) ->
                        let uu___3 = lb in
                        let uu___4 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu___5 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu___4;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu___5;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu___1
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu___3 ->
                 match uu___3 with
                 | (i, out) ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu___7, i) in
                         FStar_Syntax_Syntax.NM uu___6 in
                       uu___5 :: out in
                     ((i + Prims.int_one), uu___4)) lbs (Prims.int_zero, []) in
      match uu___ with
      | (n_let_recs, let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu___1 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu___2 ->
                             match uu___2 with
                             | (i, out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu___1 with
                    | (uu___2, u_let_rec_closing) ->
                        let uu___3 = lb in
                        let uu___4 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu___5 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___3.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu___4;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu___5;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders ->
    fun uu___ ->
      match uu___ with
      | (us, t) ->
          let n = (FStar_List.length binders) - Prims.int_one in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i ->
                 fun b ->
                   FStar_Syntax_Syntax.NM
                     ((b.FStar_Syntax_Syntax.binder_bv), (k + (n - i))))
              binders in
          let t1 = subst s t in (us, t1)
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us ->
    fun uu___ ->
      match uu___ with
      | (us', t) ->
          let n = (FStar_List.length us) - Prims.int_one in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i -> fun x -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us in
          let uu___1 = subst s t in (us', uu___1)
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | (us, t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu___1 = subst s1 t in (us, uu___1)
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs ->
    let n = (FStar_List.length bs) - Prims.int_one in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i ->
            fun b ->
              FStar_Syntax_Syntax.DB
                ((n - i), (b.FStar_Syntax_Syntax.binder_bv))))
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs -> closing_subst bs
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun b ->
    fun t ->
      let uu___ = open_term [b] t in
      match uu___ with
      | (b1::[], t1) -> (b1, t1)
      | uu___1 -> failwith "impossible: open_term_1"
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
        open_term uu___1 t in
      match uu___ with
      | (bs, t1) ->
          let uu___1 =
            FStar_List.map (fun b -> b.FStar_Syntax_Syntax.binder_bv) bs in
          (uu___1, t1)
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv ->
    fun t ->
      let uu___ = open_term_bvs [bv] t in
      match uu___ with
      | (bv1::[], t1) -> (bv1, t1)
      | uu___1 -> failwith "impossible: open_term_bv"
let rec (deep_compress :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = compress t in
    let elim_bv x =
      let uu___ = x in
      let uu___1 = deep_compress x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu___1
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar uu___ ->
        let uu___1 = t1 in
        let uu___2 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___1.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu___2
        }
    | FStar_Syntax_Syntax.Tm_constant uu___ ->
        let uu___1 = t1 in
        let uu___2 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___1.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu___2
        }
    | FStar_Syntax_Syntax.Tm_bvar uu___ ->
        let uu___1 = t1 in
        let uu___2 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___1.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu___2
        }
    | FStar_Syntax_Syntax.Tm_name uu___ ->
        let uu___1 = t1 in
        let uu___2 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___1.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu___2
        }
    | FStar_Syntax_Syntax.Tm_unknown ->
        let uu___ = t1 in
        let uu___1 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu___1
        }
    | FStar_Syntax_Syntax.Tm_uinst (f, us) ->
        let us1 = FStar_List.map deep_compress_univ us in
        mk (FStar_Syntax_Syntax.Tm_uinst (f, us1))
    | FStar_Syntax_Syntax.Tm_type u ->
        let u1 = deep_compress_univ u in mk (FStar_Syntax_Syntax.Tm_type u1)
    | FStar_Syntax_Syntax.Tm_lazy li ->
        let t2 =
          let uu___ =
            let uu___1 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
            FStar_Util.must uu___1 in
          uu___ li.FStar_Syntax_Syntax.lkind li in
        deep_compress t2
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___ =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              deep_compress in
          let uu___1 =
            deep_compress_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (rc.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu___;
            FStar_Syntax_Syntax.residual_flags = uu___1
          } in
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress_binders bs in
            let uu___3 = deep_compress t2 in
            let uu___4 = FStar_Util.map_opt rc_opt elim_rc in
            (uu___2, uu___3, uu___4) in
          FStar_Syntax_Syntax.Tm_abs uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress_binders bs in
            let uu___3 = deep_compress_comp c in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu___ =
          let uu___1 =
            let uu___2 = elim_bv bv in
            let uu___3 = deep_compress phi in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_refine uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress t2 in
            let uu___3 = deep_compress_args args in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_app uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_match (t2, asc_opt, branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___ = p in
              let uu___1 =
                let uu___2 = elim_bv x in FStar_Syntax_Syntax.Pat_var uu___2 in
              {
                FStar_Syntax_Syntax.v = uu___1;
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___ = p in
              let uu___1 =
                let uu___2 = elim_bv x in FStar_Syntax_Syntax.Pat_wild uu___2 in
              {
                FStar_Syntax_Syntax.v = uu___1;
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___ = p in
              let uu___1 =
                let uu___2 =
                  let uu___3 = elim_bv x in
                  let uu___4 = deep_compress t0 in (uu___3, uu___4) in
                FStar_Syntax_Syntax.Pat_dot_term uu___2 in
              {
                FStar_Syntax_Syntax.v = uu___1;
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___ = p in
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStar_List.map
                      (fun uu___4 ->
                         match uu___4 with
                         | (x, b) -> let uu___5 = elim_pat x in (uu___5, b))
                      pats in
                  (fv, uu___3) in
                FStar_Syntax_Syntax.Pat_cons uu___2 in
              {
                FStar_Syntax_Syntax.v = uu___1;
                FStar_Syntax_Syntax.p = (uu___.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_constant uu___ -> p in
        let elim_branch uu___ =
          match uu___ with
          | (pat, wopt, t3) ->
              let uu___1 = elim_pat pat in
              let uu___2 = FStar_Util.map_opt wopt deep_compress in
              let uu___3 = deep_compress t3 in (uu___1, uu___2, uu___3) in
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress t2 in
            let uu___3 = FStar_Util.map_opt asc_opt elim_ascription in
            let uu___4 = FStar_List.map elim_branch branches in
            (uu___2, uu___3, uu___4) in
          FStar_Syntax_Syntax.Tm_match uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress t2 in
            let uu___3 = elim_ascription a in (uu___2, uu___3, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___ =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Pervasives.Inl bv ->
                let uu___1 = elim_bv bv in FStar_Pervasives.Inl uu___1
            | FStar_Pervasives.Inr fv -> FStar_Pervasives.Inr fv in
          let uu___1 = deep_compress lb.FStar_Syntax_Syntax.lbtyp in
          let uu___2 = deep_compress lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname = uu___;
            FStar_Syntax_Syntax.lbunivs = (lb.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu___1;
            FStar_Syntax_Syntax.lbeff = (lb.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu___2;
            FStar_Syntax_Syntax.lbattrs = (lb.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos = (lb.FStar_Syntax_Syntax.lbpos)
          } in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu___3) in
            let uu___3 = deep_compress t2 in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_let uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_uvar uu___ ->
        FStar_Errors.raise_err
          (FStar_Errors.Error_UnexpectedUnresolvedUvar,
            "Internal error: unexpected unresolved uvar in deep_compress")
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 = FStar_Syntax_Syntax.on_antiquoted deep_compress qi in
        let uu___ =
          let uu___1 = let uu___2 = deep_compress tm in (uu___2, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu___ =
          let uu___1 =
            let uu___2 = deep_compress t2 in
            let uu___3 = deep_compress_meta md in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_meta uu___1 in
        mk uu___
and (elim_ascription :
  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option))
  =
  fun uu___ ->
    match uu___ with
    | (tc, topt) ->
        let uu___1 =
          match tc with
          | FStar_Pervasives.Inl t ->
              let uu___2 = deep_compress t in FStar_Pervasives.Inl uu___2
          | FStar_Pervasives.Inr c ->
              let uu___2 = deep_compress_comp c in
              FStar_Pervasives.Inr uu___2 in
        let uu___2 = FStar_Util.map_opt topt deep_compress in
        (uu___1, uu___2)
and (deep_compress_dec_order :
  FStar_Syntax_Syntax.decreases_order -> FStar_Syntax_Syntax.decreases_order)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Decreases_lex l ->
        let uu___1 = FStar_All.pipe_right l (FStar_List.map deep_compress) in
        FStar_Syntax_Syntax.Decreases_lex uu___1
    | FStar_Syntax_Syntax.Decreases_wf (rel, e) ->
        let uu___1 =
          let uu___2 = deep_compress rel in
          let uu___3 = deep_compress e in (uu___2, uu___3) in
        FStar_Syntax_Syntax.Decreases_wf uu___1
and (deep_compress_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun f ->
         match f with
         | FStar_Syntax_Syntax.DECREASES dec_order ->
             let uu___ = deep_compress_dec_order dec_order in
             FStar_Syntax_Syntax.DECREASES uu___
         | FStar_Syntax_Syntax.TOTAL -> f
         | FStar_Syntax_Syntax.MLEFFECT -> f
         | FStar_Syntax_Syntax.LEMMA -> f
         | FStar_Syntax_Syntax.RETURN -> f
         | FStar_Syntax_Syntax.PARTIAL_RETURN -> f
         | FStar_Syntax_Syntax.SOMETRIVIAL -> f
         | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> f
         | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> f
         | FStar_Syntax_Syntax.CPS -> f) flags
and (deep_compress_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uopt1 = FStar_Util.map_opt uopt deep_compress_univ in
        let uu___ =
          let uu___1 = let uu___2 = deep_compress t in (uu___2, uopt1) in
          FStar_Syntax_Syntax.Total uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uopt1 = FStar_Util.map_opt uopt deep_compress_univ in
        let uu___ =
          let uu___1 = let uu___2 = deep_compress t in (uu___2, uopt1) in
          FStar_Syntax_Syntax.GTotal uu___1 in
        mk uu___
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___ =
            FStar_List.map deep_compress_univ
              ct.FStar_Syntax_Syntax.comp_univs in
          let uu___1 = deep_compress ct.FStar_Syntax_Syntax.result_typ in
          let uu___2 = deep_compress_args ct.FStar_Syntax_Syntax.effect_args in
          let uu___3 = deep_compress_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu___;
            FStar_Syntax_Syntax.effect_name =
              (ct.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu___1;
            FStar_Syntax_Syntax.effect_args = uu___2;
            FStar_Syntax_Syntax.flags = uu___3
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (deep_compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u ->
    let u1 = compress_univ u in
    match u1 with
    | FStar_Syntax_Syntax.U_max us ->
        let uu___ = FStar_List.map deep_compress_univ us in
        FStar_Syntax_Syntax.U_max uu___
    | FStar_Syntax_Syntax.U_succ u2 ->
        let uu___ = deep_compress_univ u2 in FStar_Syntax_Syntax.U_succ uu___
    | FStar_Syntax_Syntax.U_zero -> u1
    | FStar_Syntax_Syntax.U_bvar uu___ -> u1
    | FStar_Syntax_Syntax.U_name uu___ -> u1
    | FStar_Syntax_Syntax.U_unknown -> u1
    | FStar_Syntax_Syntax.U_unif uu___ ->
        FStar_Errors.raise_err
          (FStar_Errors.Error_UnexpectedUnresolvedUvar,
            "Internal error: unexpected unresolved (universe) uvar in deep_compress")
and (deep_compress_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu___1 =
          let uu___2 = FStar_List.map deep_compress names in
          let uu___3 = FStar_List.map deep_compress_args args in
          (uu___2, uu___3) in
        FStar_Syntax_Syntax.Meta_pattern uu___1
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu___1 = let uu___2 = deep_compress t in (m, uu___2) in
        FStar_Syntax_Syntax.Meta_monadic uu___1
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu___1 = let uu___2 = deep_compress t in (m1, m2, uu___2) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu___1
    | m -> m
and (deep_compress_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  =
  fun args ->
    FStar_List.map
      (fun uu___ ->
         match uu___ with
         | (t, q) ->
             let t1 = deep_compress t in
             let q1 = deep_compress_aqual q in (t1, q1)) args
and (deep_compress_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
        let uu___ =
          let uu___1 = deep_compress t in FStar_Syntax_Syntax.Meta uu___1 in
        FStar_Pervasives_Native.Some uu___
    | uu___ -> q
and (deep_compress_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun b ->
         let x =
           let uu___ = b.FStar_Syntax_Syntax.binder_bv in
           let uu___1 =
             deep_compress
               (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
           {
             FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
             FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
             FStar_Syntax_Syntax.sort = uu___1
           } in
         let q = deep_compress_aqual b.FStar_Syntax_Syntax.binder_qual in
         let attrs =
           FStar_All.pipe_right b.FStar_Syntax_Syntax.binder_attrs
             (FStar_List.map deep_compress) in
         FStar_Syntax_Syntax.mk_binder_with_attrs x q attrs) bs