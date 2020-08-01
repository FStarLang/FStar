open Prims
let subst_to_string :
  'uuuuuu4 . (FStar_Syntax_Syntax.bv * 'uuuuuu4) Prims.list -> Prims.string =
  fun s ->
    let uu____22 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____40 ->
              match uu____40 with
              | (b, uu____46) ->
                  FStar_Ident.string_of_id b.FStar_Syntax_Syntax.ppname)) in
    FStar_All.pipe_right uu____22 (FStar_String.concat ", ")
let rec apply_until_some :
  'uuuuuu57 'uuuuuu58 .
    ('uuuuuu57 -> 'uuuuuu58 FStar_Pervasives_Native.option) ->
      'uuuuuu57 Prims.list ->
        ('uuuuuu57 Prims.list * 'uuuuuu58) FStar_Pervasives_Native.option
  =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____100 = f s0 in
          (match uu____100 with
           | FStar_Pervasives_Native.None -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry :
  'uuuuuu132 'uuuuuu133 'uuuuuu134 .
    ('uuuuuu132 -> 'uuuuuu133 -> 'uuuuuu134) ->
      'uuuuuu134 ->
        ('uuuuuu132 * 'uuuuuu133) FStar_Pervasives_Native.option ->
          'uuuuuu134
  =
  fun f ->
    fun x ->
      fun uu___0_161 ->
        match uu___0_161 with
        | FStar_Pervasives_Native.None -> x
        | FStar_Pervasives_Native.Some (a, b) -> f a b
let apply_until_some_then_map :
  'uuuuuu196 'uuuuuu197 'uuuuuu198 .
    ('uuuuuu196 -> 'uuuuuu197 FStar_Pervasives_Native.option) ->
      'uuuuuu196 Prims.list ->
        ('uuuuuu196 Prims.list -> 'uuuuuu197 -> 'uuuuuu198) ->
          'uuuuuu198 -> 'uuuuuu198
  =
  fun f ->
    fun s ->
      fun g ->
        fun t ->
          let uu____246 = apply_until_some f s in
          FStar_All.pipe_right uu____246 (map_some_curry g t)
let compose_subst :
  'uuuuuu271 .
    ('uuuuuu271 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('uuuuuu271 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('uuuuuu271 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1 ->
    fun s2 ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____322 ->
            FStar_Pervasives_Native.snd s2
        | uu____325 -> FStar_Pervasives_Native.snd s1 in
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
      | uu____384 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____407;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____408;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____409;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____410;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____411;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____412;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____413;_},
         s)
        ->
        let uu____457 = FStar_Syntax_Unionfind.find uv in
        (match uu____457 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____467 =
               let uu____470 =
                 let uu____477 = delay t' s in force_uvar' uu____477 in
               FStar_Pervasives_Native.fst uu____470 in
             (uu____467, true)
         | uu____484 -> (t, false))
    | uu____489 -> (t, false)
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____503 = force_uvar' t in
    match uu____503 with
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
        let uu____543 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____543 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____547 -> u)
    | uu____550 -> u
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___1_571 ->
           match uu___1_571 with
           | FStar_Syntax_Syntax.DB (i, x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____576 =
                 let uu____577 =
                   let uu____578 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____578 in
                 FStar_Syntax_Syntax.bv_to_name uu____577 in
               FStar_Pervasives_Native.Some uu____576
           | uu____579 -> FStar_Pervasives_Native.None)
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___2_604 ->
           match uu___2_604 with
           | FStar_Syntax_Syntax.NM (x, i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____611 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___92_616 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___92_616.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___92_616.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____611
           | FStar_Syntax_Syntax.NT (x, t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____627 -> FStar_Pervasives_Native.None)
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___3_649 ->
           match uu___3_649 with
           | FStar_Syntax_Syntax.UN (y, t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____654 -> FStar_Pervasives_Native.None)
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___4_674 ->
           match uu___4_674 with
           | FStar_Syntax_Syntax.UD (y, i) when FStar_Ident.ident_equals x y
               -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____679 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____705 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____717 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____717
      | FStar_Syntax_Syntax.U_max us ->
          let uu____721 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____721
let tag_with_range :
  'uuuuuu730 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('uuuuuu730 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____756 =
            let uu____757 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos in
            let uu____758 = FStar_Range.use_range r in
            FStar_Range.rng_included uu____757 uu____758 in
          if uu____756
          then t
          else
            (let r1 =
               let uu____763 = FStar_Range.use_range r in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____763 in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____766 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                   FStar_Syntax_Syntax.Tm_bvar uu____766
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____768 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                   FStar_Syntax_Syntax.Tm_name uu____768
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   let v =
                     let uu___144_774 = fv.FStar_Syntax_Syntax.fv_name in
                     let uu____775 = FStar_Ident.set_lid_range l r1 in
                     {
                       FStar_Syntax_Syntax.v = uu____775;
                       FStar_Syntax_Syntax.p =
                         (uu___144_774.FStar_Syntax_Syntax.p)
                     } in
                   let fv1 =
                     let uu___147_777 = fv in
                     {
                       FStar_Syntax_Syntax.fv_name = v;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___147_777.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___147_777.FStar_Syntax_Syntax.fv_qual)
                     } in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t' in
             let uu___152_779 = t in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___152_779.FStar_Syntax_Syntax.vars)
             })
let tag_lid_with_range :
  'uuuuuu788 .
    FStar_Ident.lident ->
      ('uuuuuu788 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____808 =
            let uu____809 =
              let uu____810 = FStar_Ident.range_of_lid l in
              FStar_Range.use_range uu____810 in
            let uu____811 = FStar_Range.use_range r in
            FStar_Range.rng_included uu____809 uu____811 in
          if uu____808
          then l
          else
            (let uu____813 =
               let uu____814 = FStar_Ident.range_of_lid l in
               let uu____815 = FStar_Range.use_range r in
               FStar_Range.set_use_range uu____814 uu____815 in
             FStar_Ident.set_lid_range l uu____813)
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____831 =
            let uu____832 = FStar_Range.use_range r in
            let uu____833 = FStar_Range.use_range r' in
            FStar_Range.rng_included uu____832 uu____833 in
          if uu____831
          then r
          else
            (let uu____835 = FStar_Range.use_range r' in
             FStar_Range.set_use_range r uu____835)
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
      | uu____887 ->
          let t0 = t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____893 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____898 -> tag_with_range t0 s
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
               let uu____944 =
                 let uu____945 = subst_univ (FStar_Pervasives_Native.fst s) u in
                 FStar_Syntax_Syntax.Tm_type uu____945 in
               let uu____950 = mk_range t0.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk uu____944 uu____950
           | uu____951 ->
               let uu____952 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____952)
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s ->
    fun flags ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_976 ->
              match uu___5_976 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____980 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____980
              | f -> f))
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s ->
    fun i ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____1005 =
            let uu____1006 =
              let uu____1007 = subst' s t in
              FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____1007 in
            FStar_Syntax_Syntax.Meta uu____1006 in
          FStar_Pervasives_Native.Some uu____1005
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____1013 =
            let uu____1014 =
              let uu____1015 = subst' s t in
              FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____1015 in
            FStar_Syntax_Syntax.Meta uu____1014 in
          FStar_Pervasives_Native.Some uu____1013
      | i1 -> i1
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
      | uu____1061 ->
          let uu___222_1070 = t in
          let uu____1071 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1076 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1081 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1084 =
            FStar_List.map
              (fun uu____1112 ->
                 match uu____1112 with
                 | (t1, imp) ->
                     let uu____1131 = subst' s t1 in
                     let uu____1132 = subst_imp' s imp in
                     (uu____1131, uu____1132))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1137 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1071;
            FStar_Syntax_Syntax.effect_name = uu____1076;
            FStar_Syntax_Syntax.result_typ = uu____1081;
            FStar_Syntax_Syntax.effect_args = uu____1084;
            FStar_Syntax_Syntax.flags = uu____1137
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
      | uu____1188 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1, uopt) ->
               let uu____1209 = subst' s t1 in
               let uu____1210 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1209 uu____1210
           | FStar_Syntax_Syntax.GTotal (t1, uopt) ->
               let uu____1227 = subst' s t1 in
               let uu____1228 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1227 uu____1228
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1236 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1236)
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
      | FStar_Syntax_Syntax.NT uu____1255 -> s
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n -> fun s -> FStar_List.map (shift n) s
let shift_subst' :
  'uuuuuu1278 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1278) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1278)
  =
  fun n ->
    fun s ->
      let uu____1307 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n)) in
      (uu____1307, (FStar_Pervasives_Native.snd s))
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s ->
    fun uu____1341 ->
      match uu____1341 with
      | (x, imp) ->
          let uu____1360 =
            let uu___275_1361 = x in
            let uu____1362 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___275_1361.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___275_1361.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1362
            } in
          let uu____1365 = subst_imp' s imp in (uu____1360, uu____1365)
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
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
                  (let uu____1465 = shift_subst' i s in
                   subst_binder' uu____1465 b)))
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s -> fun bs -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
let subst_arg' :
  'uuuuuu1494 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1494) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1494)
  =
  fun s ->
    fun uu____1512 ->
      match uu____1512 with
      | (t, imp) -> let uu____1519 = subst' s t in (uu____1519, imp)
let subst_args' :
  'uuuuuu1525 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1525) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1525) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____1612 -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
            let uu____1631 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1685 ->
                      fun uu____1686 ->
                        match (uu____1685, uu____1686) with
                        | ((pats1, n1), (p2, imp)) ->
                            let uu____1765 = aux n1 p2 in
                            (match uu____1765 with
                             | (p3, m) -> (((p3, imp) :: pats1), m))) 
                   ([], n)) in
            (match uu____1631 with
             | (pats1, n1) ->
                 ((let uu___312_1821 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___312_1821.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___317_1845 = x in
              let uu____1846 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___317_1845.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___317_1845.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1846
              } in
            ((let uu___320_1850 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___320_1850.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___325_1862 = x in
              let uu____1863 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___325_1862.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___325_1862.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1863
              } in
            ((let uu___328_1867 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___328_1867.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
            let s1 = shift_subst' n s in
            let x1 =
              let uu___335_1884 = x in
              let uu____1885 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___335_1884.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___335_1884.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1885
              } in
            let t01 = subst' s1 t0 in
            ((let uu___339_1890 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___339_1890.FStar_Syntax_Syntax.p)
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
          let uu____1914 =
            let uu___346_1915 = rc in
            let uu____1916 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___346_1915.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1916;
              FStar_Syntax_Syntax.residual_flags =
                (uu___346_1915.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1914
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
               (fun uu____1963 ->
                  match uu____1963 with
                  | (x', uu____1971) -> FStar_Syntax_Syntax.bv_eq x x')) in
        let rec aux uu___7_1987 =
          match uu___7_1987 with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2018 ->
                        match uu___6_2018 with
                        | FStar_Syntax_Syntax.NT (x, t) ->
                            let uu____2027 = should_retain x in
                            if uu____2027
                            then
                              let uu____2030 =
                                let uu____2031 =
                                  let uu____2038 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange) in
                                  (x, uu____2038) in
                                FStar_Syntax_Syntax.NT uu____2031 in
                              [uu____2030]
                            else []
                        | FStar_Syntax_Syntax.NM (x, i) ->
                            let uu____2050 = should_retain x in
                            if uu____2050
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___373_2056 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___373_2056.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___373_2056.FStar_Syntax_Syntax.sort)
                                   }) in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____2065 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2069 -> [])) in
              let uu____2070 = aux rest in FStar_List.append hd uu____2070 in
        let uu____2073 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s)) in
        match uu____2073 with
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
        let uu____2135 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' uu____2135 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2138 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2158 ->
               let t1 =
                 let uu____2168 =
                   let uu____2177 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                   FStar_Util.must uu____2177 in
                 uu____2168 i.FStar_Syntax_Syntax.lkind i in
               push_subst s t1
           | uu____2214 -> tag_with_range t s)
      | FStar_Syntax_Syntax.Tm_constant uu____2219 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2224 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv, s0) ->
          let uu____2251 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head in
          (match uu____2251 with
           | FStar_Pervasives_Native.None ->
               let uu____2256 =
                 let uu___406_2259 = t in
                 let uu____2262 =
                   let uu____2263 =
                     let uu____2276 = compose_uvar_subst uv s0 s in
                     (uv, uu____2276) in
                   FStar_Syntax_Syntax.Tm_uvar uu____2263 in
                 {
                   FStar_Syntax_Syntax.n = uu____2262;
                   FStar_Syntax_Syntax.pos =
                     (uu___406_2259.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___406_2259.FStar_Syntax_Syntax.vars)
                 } in
               tag_with_range uu____2256 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2300 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2301 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2302 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2316 = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1)) in
          tag_with_range uu____2316 s
      | FStar_Syntax_Syntax.Tm_app (t0, args) ->
          let uu____2351 =
            let uu____2352 =
              let uu____2369 = subst' s t0 in
              let uu____2372 = subst_args' s args in (uu____2369, uu____2372) in
            FStar_Syntax_Syntax.Tm_app uu____2352 in
          mk uu____2351
      | FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2473 = subst' s t1 in FStar_Util.Inl uu____2473
            | FStar_Util.Inr c ->
                let uu____2487 = subst_comp' s c in FStar_Util.Inr uu____2487 in
          let uu____2494 =
            let uu____2495 =
              let uu____2522 = subst' s t0 in
              let uu____2525 =
                let uu____2542 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2542) in
              (uu____2522, uu____2525, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2495 in
          mk uu____2494
      | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
          let n = FStar_List.length bs in
          let s' = shift_subst' n s in
          let uu____2624 =
            let uu____2625 =
              let uu____2644 = subst_binders' s bs in
              let uu____2653 = subst' s' body in
              let uu____2656 = push_subst_lcomp s' lopt in
              (uu____2644, uu____2653, uu____2656) in
            FStar_Syntax_Syntax.Tm_abs uu____2625 in
          mk uu____2624
      | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
          let n = FStar_List.length bs in
          let uu____2700 =
            let uu____2701 =
              let uu____2716 = subst_binders' s bs in
              let uu____2725 =
                let uu____2728 = shift_subst' n s in
                subst_comp' uu____2728 comp in
              (uu____2716, uu____2725) in
            FStar_Syntax_Syntax.Tm_arrow uu____2701 in
          mk uu____2700
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let x1 =
            let uu___453_2754 = x in
            let uu____2755 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___453_2754.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___453_2754.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2755
            } in
          let phi1 =
            let uu____2759 = shift_subst' Prims.int_one s in
            subst' uu____2759 phi in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0, pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2874 ->
                    match uu____2874 with
                    | (pat, wopt, branch) ->
                        let uu____2904 = subst_pat' s pat in
                        (match uu____2904 with
                         | (pat1, n) ->
                             let s1 = shift_subst' n s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2932 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2932 in
                             let branch1 = subst' s1 branch in
                             (pat1, wopt1, branch1)))) in
          mk (FStar_Syntax_Syntax.Tm_match (t01, pats1))
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
                      let uu____2998 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2998
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___491_3013 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___491_3013.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___491_3013.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs in
                    let uu___497_3024 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___497_3024.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___497_3024.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___497_3024.FStar_Syntax_Syntax.lbpos)
                    })) in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_pattern (bs, ps)) ->
          let uu____3074 =
            let uu____3075 =
              let uu____3082 = subst' s t0 in
              let uu____3085 =
                let uu____3086 =
                  let uu____3107 = FStar_List.map (subst' s) bs in
                  let uu____3116 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                  (uu____3107, uu____3116) in
                FStar_Syntax_Syntax.Meta_pattern uu____3086 in
              (uu____3082, uu____3085) in
            FStar_Syntax_Syntax.Tm_meta uu____3075 in
          mk uu____3074
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) ->
          let uu____3198 =
            let uu____3199 =
              let uu____3206 = subst' s t0 in
              let uu____3209 =
                let uu____3210 =
                  let uu____3217 = subst' s t1 in (m, uu____3217) in
                FStar_Syntax_Syntax.Meta_monadic uu____3210 in
              (uu____3206, uu____3209) in
            FStar_Syntax_Syntax.Tm_meta uu____3199 in
          mk uu____3198
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) ->
          let uu____3236 =
            let uu____3237 =
              let uu____3244 = subst' s t0 in
              let uu____3247 =
                let uu____3248 =
                  let uu____3257 = subst' s t1 in (m1, m2, uu____3257) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3248 in
              (uu____3244, uu____3247) in
            FStar_Syntax_Syntax.Tm_meta uu____3237 in
          mk uu____3236
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic ->
               let uu____3272 =
                 let uu____3273 =
                   let uu____3280 = subst' s tm in (uu____3280, qi) in
                 FStar_Syntax_Syntax.Tm_quoted uu____3273 in
               mk uu____3272
           | FStar_Syntax_Syntax.Quote_static ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let uu____3294 =
            let uu____3295 = let uu____3302 = subst' s t1 in (uu____3302, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3295 in
          mk uu____3294
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let t1 = force_uvar t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t', s) ->
        let uu____3345 = push_subst s t' in compress uu____3345
    | uu____3346 -> t1
and (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3348, uu____3349) ->
        let r = compress_slow t in r
    | FStar_Syntax_Syntax.Tm_uvar (uu____3373, uu____3374) ->
        let r = compress_slow t in r
    | uu____3394 -> t
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun t -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r ->
    fun t ->
      let uu____3427 =
        let uu____3428 =
          let uu____3429 =
            let uu____3430 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu____3430 in
          FStar_Syntax_Syntax.SomeUseRange uu____3429 in
        ([], uu____3428) in
      subst' uu____3427 t
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s -> fun t -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  = fun s -> fun imp -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs ->
    let uu____3488 =
      FStar_List.fold_right
        (fun uu____3513 ->
           fun uu____3514 ->
             match (uu____3513, uu____3514) with
             | ((x, uu____3546), (subst1, n)) ->
                 (((FStar_Syntax_Syntax.NM (x, n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero) in
    FStar_All.pipe_right uu____3488 FStar_Pervasives_Native.fst
let (open_binders' :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.subst_t))
  =
  fun bs ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x, imp)::bs' ->
          let x' =
            let uu___576_3673 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3674 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___576_3673.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___576_3673.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3674
            } in
          let imp1 = subst_imp o imp in
          let o1 =
            let uu____3681 = shift_subst Prims.int_one o in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3681 in
          let uu____3684 = aux bs' o1 in
          (match uu____3684 with | (bs'1, o2) -> (((x', imp1) :: bs'1), o2)) in
    aux bs []
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____3744 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3744
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs ->
    fun t ->
      let uu____3765 = open_binders' bs in
      match uu____3765 with
      | (bs', opening) ->
          let uu____3778 = subst opening t in (bs', uu____3778, opening)
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let uu____3793 = open_term' bs t in
      match uu____3793 with | (b, t1, uu____3806) -> (b, t1)
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs ->
    fun t ->
      let uu____3821 = open_binders' bs in
      match uu____3821 with
      | (bs', opening) ->
          let uu____3832 = subst_comp opening t in (bs', uu____3832)
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3881 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu____3904 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3970 ->
                    fun uu____3971 ->
                      match (uu____3970, uu____3971) with
                      | ((pats1, sub1), (p2, imp)) ->
                          let uu____4074 = open_pat_aux sub1 p2 in
                          (match uu____4074 with
                           | (p3, sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub)) in
          (match uu____3904 with
           | (pats1, sub1) ->
               ((let uu___623_4176 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___623_4176.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___627_4195 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4196 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___627_4195.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___627_4195.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4196
            } in
          let sub1 =
            let uu____4202 = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4202 in
          ((let uu___631_4210 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___631_4210.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___635_4215 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4216 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___635_4215.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___635_4215.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4216
            } in
          let sub1 =
            let uu____4222 = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4222 in
          ((let uu___639_4230 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___639_4230.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___645_4240 = x in
            let uu____4241 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___645_4240.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___645_4240.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4241
            } in
          let t01 = subst sub t0 in
          ((let uu___649_4250 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___649_4250.FStar_Syntax_Syntax.p)
            }), sub) in
    open_pat_aux [] p
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4263 ->
    match uu____4263 with
    | (p, wopt, e) ->
        let uu____4287 = open_pat p in
        (match uu____4287 with
         | (p1, opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4316 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4316 in
             let e1 = subst opening e in ((p1, wopt1, e1), opening))
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br ->
    let uu____4335 = open_branch' br in
    match uu____4335 with | (br1, uu____4341) -> br1
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs -> fun t -> let uu____4352 = closing_subst bs in subst uu____4352 t
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs ->
    fun c -> let uu____4365 = closing_subst bs in subst_comp uu____4365 c
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x, imp)::tl ->
          let x1 =
            let uu___681_4432 = x in
            let uu____4433 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___681_4432.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___681_4432.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4433
            } in
          let imp1 = subst_imp s imp in
          let s' =
            let uu____4440 = shift_subst Prims.int_one s in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4440 in
          let uu____4443 = aux s' tl in (x1, imp1) :: uu____4443 in
    aux [] bs
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p ->
    let rec aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4506 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu____4529 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4595 ->
                    fun uu____4596 ->
                      match (uu____4595, uu____4596) with
                      | ((pats1, sub1), (p2, imp)) ->
                          let uu____4699 = aux sub1 p2 in
                          (match uu____4699 with
                           | (p3, sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub)) in
          (match uu____4529 with
           | (pats1, sub1) ->
               ((let uu___708_4801 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___708_4801.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___712_4820 = x in
            let uu____4821 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___712_4820.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___712_4820.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4821
            } in
          let sub1 =
            let uu____4827 = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4827 in
          ((let uu___716_4835 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___716_4835.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___720_4840 = x in
            let uu____4841 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___720_4840.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___720_4840.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4841
            } in
          let sub1 =
            let uu____4847 = shift_subst Prims.int_one sub in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4847 in
          ((let uu___724_4855 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___724_4855.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___730_4865 = x in
            let uu____4866 = subst sub x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___730_4865.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___730_4865.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4866
            } in
          let t01 = subst sub t0 in
          ((let uu___734_4875 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___734_4875.FStar_Syntax_Syntax.p)
            }), sub) in
    aux [] p
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____4884 ->
    match uu____4884 with
    | (p, wopt, e) ->
        let uu____4904 = close_pat p in
        (match uu____4904 with
         | (p1, closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4941 = subst closing w in
                   FStar_Pervasives_Native.Some uu____4941 in
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
      let uu____5018 = univ_var_opening us in
      match uu____5018 with | (s, us') -> let t1 = subst s t in (us', t1)
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us ->
    fun c ->
      let uu____5060 = univ_var_opening us in
      match uu____5060 with
      | (s, us') -> let uu____5083 = subst_comp s c in (us', uu____5083)
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
      let uu____5139 =
        let uu____5150 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5150
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu____5183 ->
                 match uu____5183 with
                 | (i, lbs1, out) ->
                     let x =
                       let uu____5216 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5216 in
                     ((i + Prims.int_one),
                       ((let uu___786_5222 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___786_5222.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___786_5222.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___786_5222.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___786_5222.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___786_5222.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___786_5222.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], []) in
      match uu____5139 with
      | (n_let_recs, lbs1, let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb ->
                    let uu____5260 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu____5288 ->
                             match uu____5288 with
                             | (i, us, out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + Prims.int_one), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5260 with
                    | (uu____5329, us, u_let_rec_opening) ->
                        let uu___803_5340 = lb in
                        let uu____5341 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5344 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___803_5340.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5341;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___803_5340.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5344;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___803_5340.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___803_5340.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs ->
    fun t ->
      let uu____5370 =
        let uu____5377 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5377
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu____5399 ->
                 match uu____5399 with
                 | (i, out) ->
                     let uu____5418 =
                       let uu____5421 =
                         let uu____5422 =
                           let uu____5427 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5427, i) in
                         FStar_Syntax_Syntax.NM uu____5422 in
                       uu____5421 :: out in
                     ((i + Prims.int_one), uu____5418)) lbs
            (Prims.int_zero, []) in
      match uu____5370 with
      | (n_let_recs, let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____5459 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu____5477 ->
                             match uu____5477 with
                             | (i, out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5459 with
                    | (uu____5500, u_let_rec_closing) ->
                        let uu___825_5506 = lb in
                        let uu____5507 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5510 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___825_5506.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___825_5506.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5507;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___825_5506.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5510;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___825_5506.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___825_5506.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders ->
    fun uu____5525 ->
      match uu____5525 with
      | (us, t) ->
          let n = (FStar_List.length binders) - Prims.int_one in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i ->
                 fun uu____5558 ->
                   match uu____5558 with
                   | (x, uu____5566) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders in
          let t1 = subst s t in (us, t1)
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us ->
    fun uu____5585 ->
      match uu____5585 with
      | (us', t) ->
          let n = (FStar_List.length us) - Prims.int_one in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i -> fun x -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us in
          let uu____5605 = subst s t in (us', uu____5605)
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s ->
    fun uu____5623 ->
      match uu____5623 with
      | (us, t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu____5637 = subst s1 t in (us, uu____5637)
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs ->
    let n = (FStar_List.length bs) - Prims.int_one in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i ->
            fun uu____5675 ->
              match uu____5675 with
              | (x, uu____5683) -> FStar_Syntax_Syntax.DB ((n - i), x)))
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
      let uu____5707 = open_term [b] t in
      match uu____5707 with
      | (b1::[], t1) -> (b1, t1)
      | uu____5748 -> failwith "impossible: open_term_1"
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs ->
    fun t ->
      let uu____5777 =
        let uu____5782 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
        open_term uu____5782 t in
      match uu____5777 with
      | (bs, t1) ->
          let uu____5797 = FStar_List.map FStar_Pervasives_Native.fst bs in
          (uu____5797, t1)
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv ->
    fun t ->
      let uu____5824 = open_term_bvs [bv] t in
      match uu____5824 with
      | (bv1::[], t1) -> (bv1, t1)
      | uu____5839 -> failwith "impossible: open_term_bv"
let rec (deep_compress :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = compress t in
    let elim_bv x =
      let uu___887_5938 = x in
      let uu____5939 = deep_compress x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___887_5938.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index = (uu___887_5938.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____5939
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5942 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar uu____5957 ->
        let uu___900_5958 = t1 in
        let uu____5959 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___900_5958.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___900_5958.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu____5959
        }
    | FStar_Syntax_Syntax.Tm_constant uu____5964 ->
        let uu___900_5965 = t1 in
        let uu____5966 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___900_5965.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___900_5965.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu____5966
        }
    | FStar_Syntax_Syntax.Tm_bvar uu____5971 ->
        let uu___900_5972 = t1 in
        let uu____5973 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___900_5972.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___900_5972.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu____5973
        }
    | FStar_Syntax_Syntax.Tm_name uu____5978 ->
        let uu___900_5979 = t1 in
        let uu____5980 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___900_5979.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___900_5979.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu____5980
        }
    | FStar_Syntax_Syntax.Tm_unknown ->
        let uu___900_5985 = t1 in
        let uu____5986 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        {
          FStar_Syntax_Syntax.n = (uu___900_5985.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (uu___900_5985.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = uu____5986
        }
    | FStar_Syntax_Syntax.Tm_uinst (f, us) ->
        let us1 = FStar_List.map deep_compress_univ us in
        mk (FStar_Syntax_Syntax.Tm_uinst (f, us1))
    | FStar_Syntax_Syntax.Tm_type u ->
        let u1 = deep_compress_univ u in mk (FStar_Syntax_Syntax.Tm_type u1)
    | FStar_Syntax_Syntax.Tm_lazy li ->
        let t2 =
          let uu____6006 =
            let uu____6015 =
              FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
            FStar_Util.must uu____6015 in
          uu____6006 li.FStar_Syntax_Syntax.lkind li in
        deep_compress t2
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu____6085 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              deep_compress in
          let uu____6094 =
            deep_compress_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (rc.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____6085;
            FStar_Syntax_Syntax.residual_flags = uu____6094
          } in
        let uu____6097 =
          let uu____6098 =
            let uu____6117 = deep_compress_binders bs in
            let uu____6126 = deep_compress t2 in
            let uu____6129 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____6117, uu____6126, uu____6129) in
          FStar_Syntax_Syntax.Tm_abs uu____6098 in
        mk uu____6097
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____6166 =
          let uu____6167 =
            let uu____6182 = deep_compress_binders bs in
            let uu____6191 = deep_compress_comp c in (uu____6182, uu____6191) in
          FStar_Syntax_Syntax.Tm_arrow uu____6167 in
        mk uu____6166
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____6210 =
          let uu____6211 =
            let uu____6218 = elim_bv bv in
            let uu____6219 = deep_compress phi in (uu____6218, uu____6219) in
          FStar_Syntax_Syntax.Tm_refine uu____6211 in
        mk uu____6210
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____6250 =
          let uu____6251 =
            let uu____6268 = deep_compress t2 in
            let uu____6271 = deep_compress_args args in
            (uu____6268, uu____6271) in
          FStar_Syntax_Syntax.Tm_app uu____6251 in
        mk uu____6250
    | FStar_Syntax_Syntax.Tm_match (t2, branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___940_6343 = p in
              let uu____6344 =
                let uu____6345 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____6345 in
              {
                FStar_Syntax_Syntax.v = uu____6344;
                FStar_Syntax_Syntax.p = (uu___940_6343.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___944_6347 = p in
              let uu____6348 =
                let uu____6349 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____6349 in
              {
                FStar_Syntax_Syntax.v = uu____6348;
                FStar_Syntax_Syntax.p = (uu___944_6347.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___950_6356 = p in
              let uu____6357 =
                let uu____6358 =
                  let uu____6365 = elim_bv x in
                  let uu____6366 = deep_compress t0 in
                  (uu____6365, uu____6366) in
                FStar_Syntax_Syntax.Pat_dot_term uu____6358 in
              {
                FStar_Syntax_Syntax.v = uu____6357;
                FStar_Syntax_Syntax.p = (uu___950_6356.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___956_6389 = p in
              let uu____6390 =
                let uu____6391 =
                  let uu____6404 =
                    FStar_List.map
                      (fun uu____6427 ->
                         match uu____6427 with
                         | (x, b) ->
                             let uu____6440 = elim_pat x in (uu____6440, b))
                      pats in
                  (fv, uu____6404) in
                FStar_Syntax_Syntax.Pat_cons uu____6391 in
              {
                FStar_Syntax_Syntax.v = uu____6390;
                FStar_Syntax_Syntax.p = (uu___956_6389.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_constant uu____6453 -> p in
        let elim_branch uu____6477 =
          match uu____6477 with
          | (pat, wopt, t3) ->
              let uu____6503 = elim_pat pat in
              let uu____6506 = FStar_Util.map_opt wopt deep_compress in
              let uu____6509 = deep_compress t3 in
              (uu____6503, uu____6506, uu____6509) in
        let uu____6514 =
          let uu____6515 =
            let uu____6538 = deep_compress t2 in
            let uu____6541 = FStar_List.map elim_branch branches in
            (uu____6538, uu____6541) in
          FStar_Syntax_Syntax.Tm_match uu____6515 in
        mk uu____6514
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____6672 =
          match uu____6672 with
          | (tc, topt) ->
              let uu____6707 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____6717 = deep_compress t3 in
                    FStar_Util.Inl uu____6717
                | FStar_Util.Inr c ->
                    let uu____6719 = deep_compress_comp c in
                    FStar_Util.Inr uu____6719 in
              let uu____6720 = FStar_Util.map_opt topt deep_compress in
              (uu____6707, uu____6720) in
        let uu____6729 =
          let uu____6730 =
            let uu____6757 = deep_compress t2 in
            let uu____6760 = elim_ascription a in
            (uu____6757, uu____6760, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____6730 in
        mk uu____6729
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu____6821 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inl bv ->
                let uu____6831 = elim_bv bv in FStar_Util.Inl uu____6831
            | FStar_Util.Inr fv -> FStar_Util.Inr fv in
          let uu____6833 = deep_compress lb.FStar_Syntax_Syntax.lbtyp in
          let uu____6836 = deep_compress lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname = uu____6821;
            FStar_Syntax_Syntax.lbunivs = (lb.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____6833;
            FStar_Syntax_Syntax.lbeff = (lb.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____6836;
            FStar_Syntax_Syntax.lbattrs = (lb.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos = (lb.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____6839 =
          let uu____6840 =
            let uu____6853 =
              let uu____6860 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____6860) in
            let uu____6869 = deep_compress t2 in (uu____6853, uu____6869) in
          FStar_Syntax_Syntax.Tm_let uu____6840 in
        mk uu____6839
    | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 = FStar_Syntax_Syntax.on_antiquoted deep_compress qi in
        let uu____6913 =
          let uu____6914 =
            let uu____6921 = deep_compress tm in (uu____6921, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____6914 in
        mk uu____6913
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____6932 =
          let uu____6933 =
            let uu____6940 = deep_compress t2 in
            let uu____6943 = deep_compress_meta md in
            (uu____6940, uu____6943) in
          FStar_Syntax_Syntax.Tm_meta uu____6933 in
        mk uu____6932
and (deep_compress_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun f ->
         match f with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____6956 = deep_compress t in
             FStar_Syntax_Syntax.DECREASES uu____6956
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
        let uu____6981 =
          let uu____6982 =
            let uu____6991 = deep_compress t in (uu____6991, uopt1) in
          FStar_Syntax_Syntax.Total uu____6982 in
        mk uu____6981
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uopt1 = FStar_Util.map_opt uopt deep_compress_univ in
        let uu____7011 =
          let uu____7012 =
            let uu____7021 = deep_compress t in (uu____7021, uopt1) in
          FStar_Syntax_Syntax.GTotal uu____7012 in
        mk uu____7011
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu____7030 =
            FStar_List.map deep_compress_univ
              ct.FStar_Syntax_Syntax.comp_univs in
          let uu____7031 = deep_compress ct.FStar_Syntax_Syntax.result_typ in
          let uu____7034 =
            deep_compress_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____7045 = deep_compress_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____7030;
            FStar_Syntax_Syntax.effect_name =
              (ct.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____7031;
            FStar_Syntax_Syntax.effect_args = uu____7034;
            FStar_Syntax_Syntax.flags = uu____7045
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (deep_compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u ->
    let u1 = compress_univ u in
    match u1 with
    | FStar_Syntax_Syntax.U_max us ->
        let uu____7053 = FStar_List.map deep_compress_univ us in
        FStar_Syntax_Syntax.U_max uu____7053
    | FStar_Syntax_Syntax.U_succ u2 ->
        let uu____7057 = deep_compress_univ u2 in
        FStar_Syntax_Syntax.U_succ uu____7057
    | FStar_Syntax_Syntax.U_zero -> u1
    | FStar_Syntax_Syntax.U_bvar uu____7058 -> u1
    | FStar_Syntax_Syntax.U_name uu____7059 -> u1
    | FStar_Syntax_Syntax.U_unif uu____7060 -> u1
    | FStar_Syntax_Syntax.U_unknown -> u1
and (deep_compress_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___8_7071 ->
    match uu___8_7071 with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu____7106 =
          let uu____7127 = FStar_List.map deep_compress names in
          let uu____7136 = FStar_List.map deep_compress_args args in
          (uu____7127, uu____7136) in
        FStar_Syntax_Syntax.Meta_pattern uu____7106
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____7191 = let uu____7198 = deep_compress t in (m, uu____7198) in
        FStar_Syntax_Syntax.Meta_monadic uu____7191
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____7210 =
          let uu____7219 = deep_compress t in (m1, m2, uu____7219) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____7210
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
      (fun uu____7249 ->
         match uu____7249 with
         | (t, q) ->
             let t1 = deep_compress t in
             let q1 = deep_compress_aqual q in (t1, q1)) args
and (deep_compress_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
        (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
        let uu____7266 =
          let uu____7267 =
            let uu____7268 = deep_compress t in
            FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____7268 in
          FStar_Syntax_Syntax.Meta uu____7267 in
        FStar_Pervasives_Native.Some uu____7266
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
        (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
        let uu____7274 =
          let uu____7275 =
            let uu____7276 = deep_compress t in
            FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____7276 in
          FStar_Syntax_Syntax.Meta uu____7275 in
        FStar_Pervasives_Native.Some uu____7274
    | q1 -> q1
and (deep_compress_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____7302 ->
         match uu____7302 with
         | (x, q) ->
             let x1 =
               let uu___1082_7314 = x in
               let uu____7315 = deep_compress x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___1082_7314.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___1082_7314.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____7315
               } in
             let q1 = deep_compress_aqual q in (x1, q1)) bs