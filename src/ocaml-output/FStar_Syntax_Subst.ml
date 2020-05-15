open Prims
let subst_to_string :
  'uuuuuu4 . (FStar_Syntax_Syntax.bv * 'uuuuuu4) Prims.list -> Prims.string =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____44  ->
              match uu____44 with
              | (b,uu____51) ->
                  FStar_Ident.string_of_id b.FStar_Syntax_Syntax.ppname))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'uuuuuu66 'uuuuuu67 .
    ('uuuuuu66 -> 'uuuuuu67 FStar_Pervasives_Native.option) ->
      'uuuuuu66 Prims.list ->
        ('uuuuuu66 Prims.list * 'uuuuuu67) FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____109 = f s0  in
          (match uu____109 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'uuuuuu142 'uuuuuu143 'uuuuuu144 .
    ('uuuuuu142 -> 'uuuuuu143 -> 'uuuuuu144) ->
      'uuuuuu144 ->
        ('uuuuuu142 * 'uuuuuu143) FStar_Pervasives_Native.option ->
          'uuuuuu144
  =
  fun f  ->
    fun x  ->
      fun uu___0_171  ->
        match uu___0_171 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'uuuuuu207 'uuuuuu208 'uuuuuu209 .
    ('uuuuuu207 -> 'uuuuuu208 FStar_Pervasives_Native.option) ->
      'uuuuuu207 Prims.list ->
        ('uuuuuu207 Prims.list -> 'uuuuuu208 -> 'uuuuuu209) ->
          'uuuuuu209 -> 'uuuuuu209
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____257 = apply_until_some f s  in
          FStar_All.pipe_right uu____257 (map_some_curry g t)
  
let compose_subst :
  'uuuuuu283 .
    ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____334 ->
            FStar_Pervasives_Native.snd s2
        | uu____337 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed (t',s') ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____397 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____423;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____424;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____425;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____426;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____427;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____428;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____429;_},s)
        ->
        let uu____474 = FStar_Syntax_Unionfind.find uv  in
        (match uu____474 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____485 =
               let uu____488 =
                 let uu____496 = delay t' s  in force_uvar' uu____496  in
               FStar_Pervasives_Native.fst uu____488  in
             (uu____485, true)
         | uu____506 -> (t, false))
    | uu____513 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____530 = force_uvar' t  in
    match uu____530 with
    | (t',forced) ->
        if forced
        then
          delay t'
            ([],
              (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos)))
        else t
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____576 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____576 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____580 -> u)
    | uu____583 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_605  ->
           match uu___1_605 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____613 =
                 let uu____614 =
                   let uu____615 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____615  in
                 FStar_Syntax_Syntax.bv_to_name uu____614  in
               FStar_Pervasives_Native.Some uu____613
           | uu____616 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_642  ->
           match uu___2_642 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____651 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___91_656 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___91_656.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___91_656.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____651
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____667 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_692  ->
           match uu___3_692 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____700 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_721  ->
           match uu___4_721 with
           | FStar_Syntax_Syntax.UD (y,i) when FStar_Ident.ident_equals x y
               -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____728 -> FStar_Pervasives_Native.None)
  
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u  in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____756 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____768 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____768
      | FStar_Syntax_Syntax.U_max us ->
          let uu____772 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____772
  
let tag_with_range :
  'uuuuuu782 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('uuuuuu782 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____808 =
            let uu____810 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____811 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____810 uu____811  in
          if uu____808
          then t
          else
            (let r1 =
               let uu____818 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____818
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____821 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____821
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____823 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____823
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v =
                     let uu___143_829 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____830 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____830;
                       FStar_Syntax_Syntax.p =
                         (uu___143_829.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___146_832 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___146_832.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___146_832.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___151_834 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___151_834.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'uuuuuu844 .
    FStar_Ident.lident ->
      ('uuuuuu844 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____864 =
            let uu____866 =
              let uu____867 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____867  in
            let uu____868 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____866 uu____868  in
          if uu____864
          then l
          else
            (let uu____872 =
               let uu____873 = FStar_Ident.range_of_lid l  in
               let uu____874 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____873 uu____874  in
             FStar_Ident.set_lid_range l uu____872)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____891 =
            let uu____893 = FStar_Range.use_range r  in
            let uu____894 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____893 uu____894  in
          if uu____891
          then r
          else
            (let uu____898 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____898)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl = subst' (tl, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____951 ->
          let t0 = t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____957 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____962 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (t',s') ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1008 =
                 let uu____1009 =
                   subst_univ (FStar_Pervasives_Native.fst s) u  in
                 FStar_Syntax_Syntax.Tm_type uu____1009  in
               let uu____1014 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk uu____1008 uu____1014
           | uu____1015 ->
               let uu____1016 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1016)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1041  ->
              match uu___5_1041 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1045 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1045
              | f -> f))
  
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____1071 =
            let uu____1072 =
              let uu____1073 = subst' s t  in
              FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____1073  in
            FStar_Syntax_Syntax.Meta uu____1072  in
          FStar_Pervasives_Native.Some uu____1071
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____1079 =
            let uu____1080 =
              let uu____1081 = subst' s t  in
              FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____1081  in
            FStar_Syntax_Syntax.Meta uu____1080  in
          FStar_Pervasives_Native.Some uu____1079
      | i1 -> i1
  
let (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1128 ->
          let uu___221_1137 = t  in
          let uu____1138 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1143 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1148 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1151 =
            FStar_List.map
              (fun uu____1179  ->
                 match uu____1179 with
                 | (t1,imp) ->
                     let uu____1198 = subst' s t1  in
                     let uu____1199 = subst_imp' s imp  in
                     (uu____1198, uu____1199))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1204 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1138;
            FStar_Syntax_Syntax.effect_name = uu____1143;
            FStar_Syntax_Syntax.result_typ = uu____1148;
            FStar_Syntax_Syntax.effect_args = uu____1151;
            FStar_Syntax_Syntax.flags = uu____1204
          }
  
let (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1256 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1277 = subst' s t1  in
               let uu____1278 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1277 uu____1278
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1295 = subst' s t1  in
               let uu____1296 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1295 uu____1296
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1304 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1304)
  
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n))
      | FStar_Syntax_Syntax.NT uu____1338 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n  -> fun s  -> FStar_List.map (shift n) s 
let shift_subst' :
  'uuuuuu1365 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1365) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1365)
  =
  fun n  ->
    fun s  ->
      let uu____1396 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n))
         in
      (uu____1396, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1431  ->
      match uu____1431 with
      | (x,imp) ->
          let uu____1450 =
            let uu___274_1451 = x  in
            let uu____1452 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___274_1451.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___274_1451.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1452
            }  in
          let uu____1455 = subst_imp' s imp  in (uu____1450, uu____1455)
  
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = Prims.int_zero
                then subst_binder' s b
                else
                  (let uu____1561 = shift_subst' i s  in
                   subst_binder' uu____1561 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'uuuuuu1592 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1592) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1592)
  =
  fun s  ->
    fun uu____1610  ->
      match uu____1610 with
      | (t,imp) -> let uu____1617 = subst' s t  in (uu____1617, imp)
  
let subst_args' :
  'uuuuuu1624 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1624) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1624) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1718 -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1740 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1802  ->
                      fun uu____1803  ->
                        match (uu____1802, uu____1803) with
                        | ((pats1,n1),(p2,imp)) ->
                            let uu____1899 = aux n1 p2  in
                            (match uu____1899 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n))
               in
            (match uu____1740 with
             | (pats1,n1) ->
                 ((let uu___311_1973 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___311_1973.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___316_1999 = x  in
              let uu____2000 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___316_1999.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___316_1999.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2000
              }  in
            ((let uu___319_2005 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___319_2005.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___324_2018 = x  in
              let uu____2019 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___324_2018.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___324_2018.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2019
              }  in
            ((let uu___327_2024 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___327_2024.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___334_2042 = x  in
              let uu____2043 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___334_2042.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___334_2042.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2043
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___338_2049 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___338_2049.FStar_Syntax_Syntax.p)
              }), n)
         in
      aux Prims.int_zero p
  
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2075 =
            let uu___345_2076 = rc  in
            let uu____2077 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___345_2076.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2077;
              FStar_Syntax_Syntax.residual_flags =
                (uu___345_2076.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2075
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____2127  ->
                  match uu____2127 with
                  | (x',uu____2136) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2152 =
          match uu___7_2152 with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2183  ->
                        match uu___6_2183 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2192 = should_retain x  in
                            if uu____2192
                            then
                              let uu____2197 =
                                let uu____2198 =
                                  let uu____2205 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2205)  in
                                FStar_Syntax_Syntax.NT uu____2198  in
                              [uu____2197]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2220 = should_retain x  in
                            if uu____2220
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___372_2228 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___372_2228.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___372_2228.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____2238 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2243 -> []))
                 in
              let uu____2244 = aux rest  in FStar_List.append hd uu____2244
           in
        let uu____2247 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2247 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk t' =
        let uu____2310 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' uu____2310  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2313 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2334 ->
               let t1 =
                 let uu____2344 =
                   let uu____2353 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2353  in
                 uu____2344 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2403 -> tag_with_range t s)
      | FStar_Syntax_Syntax.Tm_constant uu____2408 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2413 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2440 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2440 with
           | FStar_Pervasives_Native.None  ->
               let uu____2445 =
                 let uu___405_2448 = t  in
                 let uu____2451 =
                   let uu____2452 =
                     let uu____2465 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2465)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2452  in
                 {
                   FStar_Syntax_Syntax.n = uu____2451;
                   FStar_Syntax_Syntax.pos =
                     (uu___405_2448.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___405_2448.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2445 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2489 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2490 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2491 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2505 = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1))  in
          tag_with_range uu____2505 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2540 =
            let uu____2541 =
              let uu____2558 = subst' s t0  in
              let uu____2561 = subst_args' s args  in
              (uu____2558, uu____2561)  in
            FStar_Syntax_Syntax.Tm_app uu____2541  in
          mk uu____2540
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2662 = subst' s t1  in FStar_Util.Inl uu____2662
            | FStar_Util.Inr c ->
                let uu____2676 = subst_comp' s c  in
                FStar_Util.Inr uu____2676
             in
          let uu____2683 =
            let uu____2684 =
              let uu____2711 = subst' s t0  in
              let uu____2714 =
                let uu____2731 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2731)  in
              (uu____2711, uu____2714, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2684  in
          mk uu____2683
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          let uu____2813 =
            let uu____2814 =
              let uu____2833 = subst_binders' s bs  in
              let uu____2842 = subst' s' body  in
              let uu____2845 = push_subst_lcomp s' lopt  in
              (uu____2833, uu____2842, uu____2845)  in
            FStar_Syntax_Syntax.Tm_abs uu____2814  in
          mk uu____2813
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          let uu____2889 =
            let uu____2890 =
              let uu____2905 = subst_binders' s bs  in
              let uu____2914 =
                let uu____2917 = shift_subst' n s  in
                subst_comp' uu____2917 comp  in
              (uu____2905, uu____2914)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2890  in
          mk uu____2889
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___452_2943 = x  in
            let uu____2944 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___452_2943.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___452_2943.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2944
            }  in
          let phi1 =
            let uu____2948 = shift_subst' Prims.int_one s  in
            subst' uu____2948 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3064  ->
                    match uu____3064 with
                    | (pat,wopt,branch) ->
                        let uu____3094 = subst_pat' s pat  in
                        (match uu____3094 with
                         | (pat1,n) ->
                             let s1 = shift_subst' n s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3125 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3125
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n = FStar_List.length lbs  in
          let sn = shift_subst' n s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3194 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3194
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___490_3212 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_3212.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_3212.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___496_3223 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___496_3223.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___496_3223.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___496_3223.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3275 =
            let uu____3276 =
              let uu____3283 = subst' s t0  in
              let uu____3286 =
                let uu____3287 =
                  let uu____3308 = FStar_List.map (subst' s) bs  in
                  let uu____3317 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3308, uu____3317)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3287  in
              (uu____3283, uu____3286)  in
            FStar_Syntax_Syntax.Tm_meta uu____3276  in
          mk uu____3275
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3399 =
            let uu____3400 =
              let uu____3407 = subst' s t0  in
              let uu____3410 =
                let uu____3411 =
                  let uu____3418 = subst' s t1  in (m, uu____3418)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3411  in
              (uu____3407, uu____3410)  in
            FStar_Syntax_Syntax.Tm_meta uu____3400  in
          mk uu____3399
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3437 =
            let uu____3438 =
              let uu____3445 = subst' s t0  in
              let uu____3448 =
                let uu____3449 =
                  let uu____3458 = subst' s t1  in (m1, m2, uu____3458)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3449  in
              (uu____3445, uu____3448)  in
            FStar_Syntax_Syntax.Tm_meta uu____3438  in
          mk uu____3437
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3473 =
                 let uu____3474 =
                   let uu____3481 = subst' s tm  in (uu____3481, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3474  in
               mk uu____3473
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3495 =
            let uu____3496 = let uu____3503 = subst' s t1  in (uu____3503, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3496  in
          mk uu____3495
  
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = force_uvar t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t',s) ->
        let uu____3547 = push_subst s t'  in compress uu____3547
    | uu____3548 -> t1

and (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3550,uu____3551) ->
        let r = compress_slow t  in r
    | FStar_Syntax_Syntax.Tm_uvar (uu____3575,uu____3576) ->
        let r = compress_slow t  in r
    | uu____3596 -> t

let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3631 =
        let uu____3632 =
          let uu____3633 =
            let uu____3634 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3634  in
          FStar_Syntax_Syntax.SomeUseRange uu____3633  in
        ([], uu____3632)  in
      subst' uu____3631 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  =
  fun s  -> fun imp  -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3695 =
      FStar_List.fold_right
        (fun uu____3722  ->
           fun uu____3723  ->
             match (uu____3722, uu____3723) with
             | ((x,uu____3758),(subst1,n)) ->
                 (((FStar_Syntax_Syntax.NM (x, n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____3695 FStar_Pervasives_Native.fst
  
let (open_binders' :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___575_3896 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3897 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___575_3896.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___575_3896.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3897
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____3904 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3904  in
          let uu____3910 = aux bs' o1  in
          (match uu____3910 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3971 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3971
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____3993 = open_binders' bs  in
      match uu____3993 with
      | (bs',opening) ->
          let uu____4006 = subst opening t  in (bs', uu____4006, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4022 = open_term' bs t  in
      match uu____4022 with | (b,t1,uu____4035) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4051 = open_binders' bs  in
      match uu____4051 with
      | (bs',opening) ->
          let uu____4062 = subst_comp opening t  in (bs', uu____4062)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4112 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4137 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4208  ->
                    fun uu____4209  ->
                      match (uu____4208, uu____4209) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4323 = open_pat_aux sub1 p2  in
                          (match uu____4323 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4137 with
           | (pats1,sub1) ->
               ((let uu___622_4433 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___622_4433.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___626_4454 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4455 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___626_4454.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___626_4454.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4455
            }  in
          let sub1 =
            let uu____4461 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4461  in
          ((let uu___630_4472 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___630_4472.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___634_4477 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4478 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___634_4477.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___634_4477.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4478
            }  in
          let sub1 =
            let uu____4484 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4484  in
          ((let uu___638_4495 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___638_4495.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___644_4505 = x  in
            let uu____4506 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___644_4505.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___644_4505.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4506
            }  in
          let t01 = subst sub t0  in
          ((let uu___648_4515 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___648_4515.FStar_Syntax_Syntax.p)
            }), sub)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4529  ->
    match uu____4529 with
    | (p,wopt,e) ->
        let uu____4553 = open_pat p  in
        (match uu____4553 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4582 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4582
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4602 = open_branch' br  in
    match uu____4602 with | (br1,uu____4608) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4620 = closing_subst bs  in subst uu____4620 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4634 = closing_subst bs  in subst_comp uu____4634 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl ->
          let x1 =
            let uu___680_4702 = x  in
            let uu____4703 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___680_4702.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___680_4702.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4703
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4710 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4710  in
          let uu____4716 = aux s' tl  in (x1, imp1) :: uu____4716
       in
    aux [] bs
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4780 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4805 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4876  ->
                    fun uu____4877  ->
                      match (uu____4876, uu____4877) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4991 = aux sub1 p2  in
                          (match uu____4991 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4805 with
           | (pats1,sub1) ->
               ((let uu___707_5101 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___707_5101.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___711_5122 = x  in
            let uu____5123 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___711_5122.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___711_5122.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5123
            }  in
          let sub1 =
            let uu____5129 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5129  in
          ((let uu___715_5140 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___715_5140.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___719_5145 = x  in
            let uu____5146 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___719_5145.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___719_5145.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5146
            }  in
          let sub1 =
            let uu____5152 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5152  in
          ((let uu___723_5163 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___723_5163.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___729_5173 = x  in
            let uu____5174 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___729_5173.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___729_5173.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5174
            }  in
          let t01 = subst sub t0  in
          ((let uu___733_5183 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___733_5183.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5193  ->
    match uu____5193 with
    | (p,wopt,e) ->
        let uu____5213 = close_pat p  in
        (match uu____5213 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5250 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5250
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us  ->
    let n = (FStar_List.length us) - Prims.int_one  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n = (FStar_List.length us) - Prims.int_one  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____5338 = univ_var_opening us  in
      match uu____5338 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5381 = univ_var_opening us  in
      match uu____5381 with
      | (s,us') -> let uu____5404 = subst_comp s c  in (us', uu____5404)
  
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let n = (FStar_List.length us) - Prims.int_one  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5467 =
        let uu____5479 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5479
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5519  ->
                 match uu____5519 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5556 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5556  in
                     ((i + Prims.int_one),
                       ((let uu___785_5564 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___785_5564.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___785_5564.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___785_5564.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___785_5564.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___785_5564.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___785_5564.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5467 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5607 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5637  ->
                             match uu____5637 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + Prims.int_one), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5607 with
                    | (uu____5686,us,u_let_rec_opening) ->
                        let uu___802_5699 = lb  in
                        let uu____5700 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5703 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___802_5699.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5700;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___802_5699.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5703;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___802_5699.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___802_5699.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5730 =
        let uu____5738 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5738
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5767  ->
                 match uu____5767 with
                 | (i,out) ->
                     let uu____5790 =
                       let uu____5793 =
                         let uu____5794 =
                           let uu____5800 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5800, i)  in
                         FStar_Syntax_Syntax.NM uu____5794  in
                       uu____5793 :: out  in
                     ((i + Prims.int_one), uu____5790)) lbs
            (Prims.int_zero, [])
         in
      match uu____5730 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5839 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5859  ->
                             match uu____5859 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5839 with
                    | (uu____5890,u_let_rec_closing) ->
                        let uu___824_5898 = lb  in
                        let uu____5899 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5902 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___824_5898.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___824_5898.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5899;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___824_5898.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5902;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___824_5898.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___824_5898.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5918  ->
      match uu____5918 with
      | (us,t) ->
          let n = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5953  ->
                   match uu____5953 with
                   | (x,uu____5962) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5983  ->
      match uu____5983 with
      | (us',t) ->
          let n = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let uu____6007 = subst s t  in (us', uu____6007)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6026  ->
      match uu____6026 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6040 = subst s1 t  in (us, uu____6040)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6081  ->
              match uu____6081 with
              | (x,uu____6090) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun b  ->
    fun t  ->
      let uu____6117 = open_term [b] t  in
      match uu____6117 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6158 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6189 =
        let uu____6194 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6194 t  in
      match uu____6189 with
      | (bs,t1) ->
          let uu____6209 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6209, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6237 = open_term_bvs [bv] t  in
      match uu____6237 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6252 -> failwith "impossible: open_term_bv"
  