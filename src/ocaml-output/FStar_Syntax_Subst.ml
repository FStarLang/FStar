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
                  FStar_Ident.text_of_id b.FStar_Syntax_Syntax.ppname))
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
        let uu____478 = FStar_Syntax_Unionfind.find uv  in
        (match uu____478 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____489 =
               let uu____492 =
                 let uu____500 = delay t' s  in force_uvar' uu____500  in
               FStar_Pervasives_Native.fst uu____492  in
             (uu____489, true)
         | uu____510 -> (t, false))
    | uu____517 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____534 = force_uvar' t  in
    match uu____534 with
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
        let uu____578 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____578 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____582 -> u)
    | uu____585 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_607  ->
           match uu___1_607 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____615 =
                 let uu____616 =
                   let uu____617 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____617  in
                 FStar_Syntax_Syntax.bv_to_name uu____616  in
               FStar_Pervasives_Native.Some uu____615
           | uu____618 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_644  ->
           match uu___2_644 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____653 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___91_658 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___91_658.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___91_658.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____653
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____669 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_694  ->
           match uu___3_694 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____702 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_723  ->
           match uu___4_723 with
           | FStar_Syntax_Syntax.UD (y,i) when FStar_Ident.ident_equals x y
               -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____730 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____758 -> u1
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
               let uu____1008 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1009 =
                 let uu____1016 =
                   let uu____1017 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1017  in
                 FStar_Syntax_Syntax.mk uu____1016  in
               uu____1009 FStar_Pervasives_Native.None uu____1008
           | uu____1022 ->
               let uu____1023 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1023)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1048  ->
              match uu___5_1048 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1052 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1052
              | f -> f))
  
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1078 =
            let uu____1079 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1079  in
          FStar_Pervasives_Native.Some uu____1078
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
      | uu____1126 ->
          let uu___216_1135 = t  in
          let uu____1136 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1141 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1146 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1149 =
            FStar_List.map
              (fun uu____1177  ->
                 match uu____1177 with
                 | (t1,imp) ->
                     let uu____1196 = subst' s t1  in
                     let uu____1197 = subst_imp' s imp  in
                     (uu____1196, uu____1197))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1202 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1136;
            FStar_Syntax_Syntax.effect_name = uu____1141;
            FStar_Syntax_Syntax.result_typ = uu____1146;
            FStar_Syntax_Syntax.effect_args = uu____1149;
            FStar_Syntax_Syntax.flags = uu____1202
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
      | uu____1254 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1275 = subst' s t1  in
               let uu____1276 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1275 uu____1276
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1293 = subst' s t1  in
               let uu____1294 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1293 uu____1294
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1302 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1302)
  
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
      | FStar_Syntax_Syntax.NT uu____1336 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n  -> fun s  -> FStar_List.map (shift n) s 
let shift_subst' :
  'uuuuuu1363 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1363) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1363)
  =
  fun n  ->
    fun s  ->
      let uu____1394 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n))
         in
      (uu____1394, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1429  ->
      match uu____1429 with
      | (x,imp) ->
          let uu____1448 =
            let uu___269_1449 = x  in
            let uu____1450 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___269_1449.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___269_1449.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1450
            }  in
          let uu____1453 = subst_imp' s imp  in (uu____1448, uu____1453)
  
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
                  (let uu____1559 = shift_subst' i s  in
                   subst_binder' uu____1559 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'uuuuuu1590 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1590) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1590)
  =
  fun s  ->
    fun uu____1608  ->
      match uu____1608 with
      | (t,imp) -> let uu____1615 = subst' s t  in (uu____1615, imp)
  
let subst_args' :
  'uuuuuu1622 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1622) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1622) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____1716 -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1738 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1800  ->
                      fun uu____1801  ->
                        match (uu____1800, uu____1801) with
                        | ((pats1,n1),(p2,imp)) ->
                            let uu____1897 = aux n1 p2  in
                            (match uu____1897 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n))
               in
            (match uu____1738 with
             | (pats1,n1) ->
                 ((let uu___306_1971 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___306_1971.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___311_1997 = x  in
              let uu____1998 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___311_1997.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___311_1997.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1998
              }  in
            ((let uu___314_2003 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___314_2003.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___319_2016 = x  in
              let uu____2017 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___319_2016.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___319_2016.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2017
              }  in
            ((let uu___322_2022 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___322_2022.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___329_2040 = x  in
              let uu____2041 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___329_2040.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___329_2040.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2041
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___333_2047 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___333_2047.FStar_Syntax_Syntax.p)
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
          let uu____2073 =
            let uu___340_2074 = rc  in
            let uu____2075 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___340_2074.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2075;
              FStar_Syntax_Syntax.residual_flags =
                (uu___340_2074.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2073
  
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
               (fun uu____2125  ->
                  match uu____2125 with
                  | (x',uu____2134) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2150 =
          match uu___7_2150 with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2181  ->
                        match uu___6_2181 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2190 = should_retain x  in
                            if uu____2190
                            then
                              let uu____2195 =
                                let uu____2196 =
                                  let uu____2203 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2203)  in
                                FStar_Syntax_Syntax.NT uu____2196  in
                              [uu____2195]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2218 = should_retain x  in
                            if uu____2218
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___367_2226 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___367_2226.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___367_2226.FStar_Syntax_Syntax.sort)
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
                               | uu____2236 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2241 -> []))
                 in
              let uu____2242 = aux rest  in FStar_List.append hd uu____2242
           in
        let uu____2245 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2245 with
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
        let uu____2308 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2308  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2311 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2332 ->
               let t1 =
                 let uu____2342 =
                   let uu____2351 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2351  in
                 uu____2342 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2401 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2402 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2407 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2434 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2434 with
           | FStar_Pervasives_Native.None  ->
               let uu____2439 =
                 let uu___400_2442 = t  in
                 let uu____2445 =
                   let uu____2446 =
                     let uu____2459 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2459)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2446  in
                 {
                   FStar_Syntax_Syntax.n = uu____2445;
                   FStar_Syntax_Syntax.pos =
                     (uu___400_2442.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___400_2442.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2439 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2483 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2484 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2485 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2499 = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1))  in
          tag_with_range uu____2499 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2534 =
            let uu____2535 =
              let uu____2552 = subst' s t0  in
              let uu____2555 = subst_args' s args  in
              (uu____2552, uu____2555)  in
            FStar_Syntax_Syntax.Tm_app uu____2535  in
          mk uu____2534
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2656 = subst' s t1  in FStar_Util.Inl uu____2656
            | FStar_Util.Inr c ->
                let uu____2670 = subst_comp' s c  in
                FStar_Util.Inr uu____2670
             in
          let uu____2677 =
            let uu____2678 =
              let uu____2705 = subst' s t0  in
              let uu____2708 =
                let uu____2725 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2725)  in
              (uu____2705, uu____2708, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2678  in
          mk uu____2677
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          let uu____2807 =
            let uu____2808 =
              let uu____2827 = subst_binders' s bs  in
              let uu____2836 = subst' s' body  in
              let uu____2839 = push_subst_lcomp s' lopt  in
              (uu____2827, uu____2836, uu____2839)  in
            FStar_Syntax_Syntax.Tm_abs uu____2808  in
          mk uu____2807
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          let uu____2883 =
            let uu____2884 =
              let uu____2899 = subst_binders' s bs  in
              let uu____2908 =
                let uu____2911 = shift_subst' n s  in
                subst_comp' uu____2911 comp  in
              (uu____2899, uu____2908)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2884  in
          mk uu____2883
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___447_2937 = x  in
            let uu____2938 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___447_2937.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___447_2937.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2938
            }  in
          let phi1 =
            let uu____2942 = shift_subst' Prims.int_one s  in
            subst' uu____2942 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3058  ->
                    match uu____3058 with
                    | (pat,wopt,branch) ->
                        let uu____3088 = subst_pat' s pat  in
                        (match uu____3088 with
                         | (pat1,n) ->
                             let s1 = shift_subst' n s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3119 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3119
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
                      let uu____3188 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3188
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___485_3206 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___485_3206.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___485_3206.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___491_3217 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___491_3217.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___491_3217.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___491_3217.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3269 =
            let uu____3270 =
              let uu____3277 = subst' s t0  in
              let uu____3280 =
                let uu____3281 =
                  let uu____3302 = FStar_List.map (subst' s) bs  in
                  let uu____3311 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3302, uu____3311)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3281  in
              (uu____3277, uu____3280)  in
            FStar_Syntax_Syntax.Tm_meta uu____3270  in
          mk uu____3269
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3393 =
            let uu____3394 =
              let uu____3401 = subst' s t0  in
              let uu____3404 =
                let uu____3405 =
                  let uu____3412 = subst' s t1  in (m, uu____3412)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3405  in
              (uu____3401, uu____3404)  in
            FStar_Syntax_Syntax.Tm_meta uu____3394  in
          mk uu____3393
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3431 =
            let uu____3432 =
              let uu____3439 = subst' s t0  in
              let uu____3442 =
                let uu____3443 =
                  let uu____3452 = subst' s t1  in (m1, m2, uu____3452)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3443  in
              (uu____3439, uu____3442)  in
            FStar_Syntax_Syntax.Tm_meta uu____3432  in
          mk uu____3431
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3467 =
                 let uu____3468 =
                   let uu____3475 = subst' s tm  in (uu____3475, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3468  in
               mk uu____3467
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3489 =
            let uu____3490 = let uu____3497 = subst' s t1  in (uu____3497, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3490  in
          mk uu____3489
  
let (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = force_uvar t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t',s) -> push_subst s t'
    | uu____3537 -> t1
  
let (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3544,uu____3545) ->
        compress_slow t
    | FStar_Syntax_Syntax.Tm_uvar (uu____3566,uu____3567) -> compress_slow t
    | uu____3584 -> t
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3619 =
        let uu____3620 =
          let uu____3621 =
            let uu____3622 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3622  in
          FStar_Syntax_Syntax.SomeUseRange uu____3621  in
        ([], uu____3620)  in
      subst' uu____3619 t
  
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
    let uu____3683 =
      FStar_List.fold_right
        (fun uu____3710  ->
           fun uu____3711  ->
             match (uu____3710, uu____3711) with
             | ((x,uu____3746),(subst1,n)) ->
                 (((FStar_Syntax_Syntax.NM (x, n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____3683 FStar_Pervasives_Native.fst
  
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
            let uu___569_3884 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3885 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___569_3884.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___569_3884.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3885
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____3892 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3892  in
          let uu____3898 = aux bs' o1  in
          (match uu____3898 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3959 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3959
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____3981 = open_binders' bs  in
      match uu____3981 with
      | (bs',opening) ->
          let uu____3994 = subst opening t  in (bs', uu____3994, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4010 = open_term' bs t  in
      match uu____4010 with | (b,t1,uu____4023) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4039 = open_binders' bs  in
      match uu____4039 with
      | (bs',opening) ->
          let uu____4050 = subst_comp opening t  in (bs', uu____4050)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4100 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4125 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4196  ->
                    fun uu____4197  ->
                      match (uu____4196, uu____4197) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4311 = open_pat_aux sub1 p2  in
                          (match uu____4311 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4125 with
           | (pats1,sub1) ->
               ((let uu___616_4421 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___616_4421.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___620_4442 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4443 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___620_4442.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___620_4442.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4443
            }  in
          let sub1 =
            let uu____4449 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4449  in
          ((let uu___624_4460 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___624_4460.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___628_4465 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4466 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___628_4465.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___628_4465.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4466
            }  in
          let sub1 =
            let uu____4472 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4472  in
          ((let uu___632_4483 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___632_4483.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___638_4493 = x  in
            let uu____4494 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___638_4493.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___638_4493.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4494
            }  in
          let t01 = subst sub t0  in
          ((let uu___642_4503 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___642_4503.FStar_Syntax_Syntax.p)
            }), sub)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4517  ->
    match uu____4517 with
    | (p,wopt,e) ->
        let uu____4541 = open_pat p  in
        (match uu____4541 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4570 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4570
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4590 = open_branch' br  in
    match uu____4590 with | (br1,uu____4596) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4608 = closing_subst bs  in subst uu____4608 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4622 = closing_subst bs  in subst_comp uu____4622 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl ->
          let x1 =
            let uu___674_4690 = x  in
            let uu____4691 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___674_4690.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___674_4690.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4691
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4698 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4698  in
          let uu____4704 = aux s' tl  in (x1, imp1) :: uu____4704
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
      | FStar_Syntax_Syntax.Pat_constant uu____4768 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4793 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4864  ->
                    fun uu____4865  ->
                      match (uu____4864, uu____4865) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4979 = aux sub1 p2  in
                          (match uu____4979 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4793 with
           | (pats1,sub1) ->
               ((let uu___701_5089 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___701_5089.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___705_5110 = x  in
            let uu____5111 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___705_5110.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___705_5110.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5111
            }  in
          let sub1 =
            let uu____5117 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5117  in
          ((let uu___709_5128 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___709_5128.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___713_5133 = x  in
            let uu____5134 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___713_5133.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___713_5133.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5134
            }  in
          let sub1 =
            let uu____5140 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5140  in
          ((let uu___717_5151 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___717_5151.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___723_5161 = x  in
            let uu____5162 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___723_5161.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___723_5161.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5162
            }  in
          let t01 = subst sub t0  in
          ((let uu___727_5171 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___727_5171.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5181  ->
    match uu____5181 with
    | (p,wopt,e) ->
        let uu____5201 = close_pat p  in
        (match uu____5201 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5238 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5238
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
      let uu____5326 = univ_var_opening us  in
      match uu____5326 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5369 = univ_var_opening us  in
      match uu____5369 with
      | (s,us') -> let uu____5392 = subst_comp s c  in (us', uu____5392)
  
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
      let uu____5455 =
        let uu____5467 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5467
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5507  ->
                 match uu____5507 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5544 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5544  in
                     ((i + Prims.int_one),
                       ((let uu___779_5552 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___779_5552.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___779_5552.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___779_5552.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___779_5552.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___779_5552.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___779_5552.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5455 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5595 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5625  ->
                             match uu____5625 with
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
                    match uu____5595 with
                    | (uu____5674,us,u_let_rec_opening) ->
                        let uu___796_5687 = lb  in
                        let uu____5688 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5691 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___796_5687.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5688;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___796_5687.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5691;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___796_5687.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___796_5687.FStar_Syntax_Syntax.lbpos)
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
      let uu____5718 =
        let uu____5726 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5726
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5755  ->
                 match uu____5755 with
                 | (i,out) ->
                     let uu____5778 =
                       let uu____5781 =
                         let uu____5782 =
                           let uu____5788 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5788, i)  in
                         FStar_Syntax_Syntax.NM uu____5782  in
                       uu____5781 :: out  in
                     ((i + Prims.int_one), uu____5778)) lbs
            (Prims.int_zero, [])
         in
      match uu____5718 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5827 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5847  ->
                             match uu____5847 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5827 with
                    | (uu____5878,u_let_rec_closing) ->
                        let uu___818_5886 = lb  in
                        let uu____5887 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5890 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___818_5886.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___818_5886.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5887;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___818_5886.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5890;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___818_5886.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___818_5886.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5906  ->
      match uu____5906 with
      | (us,t) ->
          let n = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5941  ->
                   match uu____5941 with
                   | (x,uu____5950) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5971  ->
      match uu____5971 with
      | (us',t) ->
          let n = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let uu____5995 = subst s t  in (us', uu____5995)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6014  ->
      match uu____6014 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6028 = subst s1 t  in (us, uu____6028)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6069  ->
              match uu____6069 with
              | (x,uu____6078) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  
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
      let uu____6105 = open_term [b] t  in
      match uu____6105 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6146 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6177 =
        let uu____6182 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6182 t  in
      match uu____6177 with
      | (bs,t1) ->
          let uu____6197 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6197, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6225 = open_term_bvs [bv] t  in
      match uu____6225 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6240 -> failwith "impossible: open_term_bv"
  