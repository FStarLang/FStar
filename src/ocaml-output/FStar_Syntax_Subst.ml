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
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
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
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____731 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____759 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____769 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____769
      | FStar_Syntax_Syntax.U_max us ->
          let uu____773 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____773
  
let tag_with_range :
  'uuuuuu783 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('uuuuuu783 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____809 =
            let uu____811 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____812 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____811 uu____812  in
          if uu____809
          then t
          else
            (let r1 =
               let uu____819 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____819
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____822 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____822
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____824 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____824
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v =
                     let uu___143_830 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____831 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____831;
                       FStar_Syntax_Syntax.p =
                         (uu___143_830.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___146_833 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___146_833.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___146_833.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___151_835 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___151_835.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'uuuuuu845 .
    FStar_Ident.lident ->
      ('uuuuuu845 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____865 =
            let uu____867 =
              let uu____868 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____868  in
            let uu____869 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____867 uu____869  in
          if uu____865
          then l
          else
            (let uu____873 =
               let uu____874 = FStar_Ident.range_of_lid l  in
               let uu____875 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____874 uu____875  in
             FStar_Ident.set_lid_range l uu____873)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____892 =
            let uu____894 = FStar_Range.use_range r  in
            let uu____895 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____894 uu____895  in
          if uu____892
          then r
          else
            (let uu____899 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____899)
  
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
      | uu____952 ->
          let t0 = t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____958 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____963 -> tag_with_range t0 s
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
               let uu____1009 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1010 =
                 let uu____1017 =
                   let uu____1018 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1018  in
                 FStar_Syntax_Syntax.mk uu____1017  in
               uu____1010 FStar_Pervasives_Native.None uu____1009
           | uu____1023 ->
               let uu____1024 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1024)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1049  ->
              match uu___5_1049 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1053 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1053
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
          let uu____1079 =
            let uu____1080 = subst' s t  in
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
      | uu____1127 ->
          let uu___216_1136 = t  in
          let uu____1137 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1142 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1147 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1150 =
            FStar_List.map
              (fun uu____1178  ->
                 match uu____1178 with
                 | (t1,imp) ->
                     let uu____1197 = subst' s t1  in
                     let uu____1198 = subst_imp' s imp  in
                     (uu____1197, uu____1198))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1203 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1137;
            FStar_Syntax_Syntax.effect_name = uu____1142;
            FStar_Syntax_Syntax.result_typ = uu____1147;
            FStar_Syntax_Syntax.effect_args = uu____1150;
            FStar_Syntax_Syntax.flags = uu____1203
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
      | uu____1255 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1276 = subst' s t1  in
               let uu____1277 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1276 uu____1277
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1294 = subst' s t1  in
               let uu____1295 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1294 uu____1295
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1303 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1303)
  
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
      | FStar_Syntax_Syntax.NT uu____1337 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n  -> fun s  -> FStar_List.map (shift n) s 
let shift_subst' :
  'uuuuuu1364 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1364) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1364)
  =
  fun n  ->
    fun s  ->
      let uu____1395 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n))
         in
      (uu____1395, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1430  ->
      match uu____1430 with
      | (x,imp) ->
          let uu____1449 =
            let uu___269_1450 = x  in
            let uu____1451 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___269_1450.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___269_1450.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1451
            }  in
          let uu____1454 = subst_imp' s imp  in (uu____1449, uu____1454)
  
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
                  (let uu____1560 = shift_subst' i s  in
                   subst_binder' uu____1560 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'uuuuuu1591 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1591) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1591)
  =
  fun s  ->
    fun uu____1609  ->
      match uu____1609 with
      | (t,imp) -> let uu____1616 = subst' s t  in (uu____1616, imp)
  
let subst_args' :
  'uuuuuu1623 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1623) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1623) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____1717 -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1739 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1801  ->
                      fun uu____1802  ->
                        match (uu____1801, uu____1802) with
                        | ((pats1,n1),(p2,imp)) ->
                            let uu____1898 = aux n1 p2  in
                            (match uu____1898 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n))
               in
            (match uu____1739 with
             | (pats1,n1) ->
                 ((let uu___306_1972 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___306_1972.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___311_1998 = x  in
              let uu____1999 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___311_1998.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___311_1998.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1999
              }  in
            ((let uu___314_2004 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___314_2004.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___319_2017 = x  in
              let uu____2018 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___319_2017.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___319_2017.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2018
              }  in
            ((let uu___322_2023 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___322_2023.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___329_2041 = x  in
              let uu____2042 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___329_2041.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___329_2041.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2042
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___333_2048 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___333_2048.FStar_Syntax_Syntax.p)
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
          let uu____2074 =
            let uu___340_2075 = rc  in
            let uu____2076 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___340_2075.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2076;
              FStar_Syntax_Syntax.residual_flags =
                (uu___340_2075.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2074
  
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
               (fun uu____2126  ->
                  match uu____2126 with
                  | (x',uu____2135) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2151 =
          match uu___7_2151 with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2182  ->
                        match uu___6_2182 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2191 = should_retain x  in
                            if uu____2191
                            then
                              let uu____2196 =
                                let uu____2197 =
                                  let uu____2204 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2204)  in
                                FStar_Syntax_Syntax.NT uu____2197  in
                              [uu____2196]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2219 = should_retain x  in
                            if uu____2219
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___367_2227 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___367_2227.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___367_2227.FStar_Syntax_Syntax.sort)
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
                               | uu____2237 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2242 -> []))
                 in
              let uu____2243 = aux rest  in FStar_List.append hd uu____2243
           in
        let uu____2246 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2246 with
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
        let uu____2309 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2309  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2312 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2333 ->
               let t1 =
                 let uu____2343 =
                   let uu____2352 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2352  in
                 uu____2343 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2402 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2403 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2408 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2435 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2435 with
           | FStar_Pervasives_Native.None  ->
               let uu____2440 =
                 let uu___400_2443 = t  in
                 let uu____2446 =
                   let uu____2447 =
                     let uu____2460 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2460)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2447  in
                 {
                   FStar_Syntax_Syntax.n = uu____2446;
                   FStar_Syntax_Syntax.pos =
                     (uu___400_2443.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___400_2443.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2440 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2484 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2485 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2486 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2500 = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1))  in
          tag_with_range uu____2500 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2535 =
            let uu____2536 =
              let uu____2553 = subst' s t0  in
              let uu____2556 = subst_args' s args  in
              (uu____2553, uu____2556)  in
            FStar_Syntax_Syntax.Tm_app uu____2536  in
          mk uu____2535
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2657 = subst' s t1  in FStar_Util.Inl uu____2657
            | FStar_Util.Inr c ->
                let uu____2671 = subst_comp' s c  in
                FStar_Util.Inr uu____2671
             in
          let uu____2678 =
            let uu____2679 =
              let uu____2706 = subst' s t0  in
              let uu____2709 =
                let uu____2726 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2726)  in
              (uu____2706, uu____2709, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2679  in
          mk uu____2678
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          let uu____2808 =
            let uu____2809 =
              let uu____2828 = subst_binders' s bs  in
              let uu____2837 = subst' s' body  in
              let uu____2840 = push_subst_lcomp s' lopt  in
              (uu____2828, uu____2837, uu____2840)  in
            FStar_Syntax_Syntax.Tm_abs uu____2809  in
          mk uu____2808
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          let uu____2884 =
            let uu____2885 =
              let uu____2900 = subst_binders' s bs  in
              let uu____2909 =
                let uu____2912 = shift_subst' n s  in
                subst_comp' uu____2912 comp  in
              (uu____2900, uu____2909)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2885  in
          mk uu____2884
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___447_2938 = x  in
            let uu____2939 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___447_2938.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___447_2938.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2939
            }  in
          let phi1 =
            let uu____2943 = shift_subst' Prims.int_one s  in
            subst' uu____2943 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3059  ->
                    match uu____3059 with
                    | (pat,wopt,branch) ->
                        let uu____3089 = subst_pat' s pat  in
                        (match uu____3089 with
                         | (pat1,n) ->
                             let s1 = shift_subst' n s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3120 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3120
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
                      let uu____3189 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3189
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___485_3207 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___485_3207.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___485_3207.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___491_3218 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___491_3218.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___491_3218.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___491_3218.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3270 =
            let uu____3271 =
              let uu____3278 = subst' s t0  in
              let uu____3281 =
                let uu____3282 =
                  let uu____3303 = FStar_List.map (subst' s) bs  in
                  let uu____3312 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3303, uu____3312)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3282  in
              (uu____3278, uu____3281)  in
            FStar_Syntax_Syntax.Tm_meta uu____3271  in
          mk uu____3270
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3394 =
            let uu____3395 =
              let uu____3402 = subst' s t0  in
              let uu____3405 =
                let uu____3406 =
                  let uu____3413 = subst' s t1  in (m, uu____3413)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3406  in
              (uu____3402, uu____3405)  in
            FStar_Syntax_Syntax.Tm_meta uu____3395  in
          mk uu____3394
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3432 =
            let uu____3433 =
              let uu____3440 = subst' s t0  in
              let uu____3443 =
                let uu____3444 =
                  let uu____3453 = subst' s t1  in (m1, m2, uu____3453)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3444  in
              (uu____3440, uu____3443)  in
            FStar_Syntax_Syntax.Tm_meta uu____3433  in
          mk uu____3432
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3468 =
                 let uu____3469 =
                   let uu____3476 = subst' s tm  in (uu____3476, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3469  in
               mk uu____3468
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3490 =
            let uu____3491 = let uu____3498 = subst' s t1  in (uu____3498, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3491  in
          mk uu____3490
  
let (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = force_uvar t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t',s) -> push_subst s t'
    | uu____3538 -> t1
  
let (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3545,uu____3546) ->
        compress_slow t
    | FStar_Syntax_Syntax.Tm_uvar (uu____3567,uu____3568) -> compress_slow t
    | uu____3585 -> t
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3620 =
        let uu____3621 =
          let uu____3622 =
            let uu____3623 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3623  in
          FStar_Syntax_Syntax.SomeUseRange uu____3622  in
        ([], uu____3621)  in
      subst' uu____3620 t
  
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
    let uu____3684 =
      FStar_List.fold_right
        (fun uu____3711  ->
           fun uu____3712  ->
             match (uu____3711, uu____3712) with
             | ((x,uu____3747),(subst1,n)) ->
                 (((FStar_Syntax_Syntax.NM (x, n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____3684 FStar_Pervasives_Native.fst
  
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
            let uu___569_3885 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3886 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___569_3885.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___569_3885.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3886
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____3893 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3893  in
          let uu____3899 = aux bs' o1  in
          (match uu____3899 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3960 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3960
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____3982 = open_binders' bs  in
      match uu____3982 with
      | (bs',opening) ->
          let uu____3995 = subst opening t  in (bs', uu____3995, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4011 = open_term' bs t  in
      match uu____4011 with | (b,t1,uu____4024) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4040 = open_binders' bs  in
      match uu____4040 with
      | (bs',opening) ->
          let uu____4051 = subst_comp opening t  in (bs', uu____4051)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4101 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4126 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4197  ->
                    fun uu____4198  ->
                      match (uu____4197, uu____4198) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4312 = open_pat_aux sub1 p2  in
                          (match uu____4312 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4126 with
           | (pats1,sub1) ->
               ((let uu___616_4422 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___616_4422.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___620_4443 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4444 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___620_4443.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___620_4443.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4444
            }  in
          let sub1 =
            let uu____4450 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4450  in
          ((let uu___624_4461 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___624_4461.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___628_4466 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4467 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___628_4466.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___628_4466.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4467
            }  in
          let sub1 =
            let uu____4473 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4473  in
          ((let uu___632_4484 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___632_4484.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___638_4494 = x  in
            let uu____4495 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___638_4494.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___638_4494.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4495
            }  in
          let t01 = subst sub t0  in
          ((let uu___642_4504 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___642_4504.FStar_Syntax_Syntax.p)
            }), sub)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4518  ->
    match uu____4518 with
    | (p,wopt,e) ->
        let uu____4542 = open_pat p  in
        (match uu____4542 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4571 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4571
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4591 = open_branch' br  in
    match uu____4591 with | (br1,uu____4597) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4609 = closing_subst bs  in subst uu____4609 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4623 = closing_subst bs  in subst_comp uu____4623 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl ->
          let x1 =
            let uu___674_4691 = x  in
            let uu____4692 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___674_4691.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___674_4691.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4692
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4699 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4699  in
          let uu____4705 = aux s' tl  in (x1, imp1) :: uu____4705
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
      | FStar_Syntax_Syntax.Pat_constant uu____4769 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4794 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4865  ->
                    fun uu____4866  ->
                      match (uu____4865, uu____4866) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4980 = aux sub1 p2  in
                          (match uu____4980 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4794 with
           | (pats1,sub1) ->
               ((let uu___701_5090 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___701_5090.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___705_5111 = x  in
            let uu____5112 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___705_5111.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___705_5111.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5112
            }  in
          let sub1 =
            let uu____5118 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5118  in
          ((let uu___709_5129 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___709_5129.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___713_5134 = x  in
            let uu____5135 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___713_5134.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___713_5134.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5135
            }  in
          let sub1 =
            let uu____5141 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5141  in
          ((let uu___717_5152 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___717_5152.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___723_5162 = x  in
            let uu____5163 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___723_5162.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___723_5162.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5163
            }  in
          let t01 = subst sub t0  in
          ((let uu___727_5172 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___727_5172.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5182  ->
    match uu____5182 with
    | (p,wopt,e) ->
        let uu____5202 = close_pat p  in
        (match uu____5202 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5239 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5239
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
      let uu____5327 = univ_var_opening us  in
      match uu____5327 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5370 = univ_var_opening us  in
      match uu____5370 with
      | (s,us') -> let uu____5393 = subst_comp s c  in (us', uu____5393)
  
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
      let uu____5456 =
        let uu____5468 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5468
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5508  ->
                 match uu____5508 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5545 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5545  in
                     ((i + Prims.int_one),
                       ((let uu___779_5553 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___779_5553.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___779_5553.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___779_5553.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___779_5553.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___779_5553.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___779_5553.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5456 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5596 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5626  ->
                             match uu____5626 with
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
                    match uu____5596 with
                    | (uu____5675,us,u_let_rec_opening) ->
                        let uu___796_5688 = lb  in
                        let uu____5689 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5692 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___796_5688.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5689;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___796_5688.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5692;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___796_5688.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___796_5688.FStar_Syntax_Syntax.lbpos)
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
      let uu____5719 =
        let uu____5727 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5727
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5756  ->
                 match uu____5756 with
                 | (i,out) ->
                     let uu____5779 =
                       let uu____5782 =
                         let uu____5783 =
                           let uu____5789 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5789, i)  in
                         FStar_Syntax_Syntax.NM uu____5783  in
                       uu____5782 :: out  in
                     ((i + Prims.int_one), uu____5779)) lbs
            (Prims.int_zero, [])
         in
      match uu____5719 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5828 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5848  ->
                             match uu____5848 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5828 with
                    | (uu____5879,u_let_rec_closing) ->
                        let uu___818_5887 = lb  in
                        let uu____5888 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5891 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___818_5887.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___818_5887.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5888;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___818_5887.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5891;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___818_5887.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___818_5887.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5907  ->
      match uu____5907 with
      | (us,t) ->
          let n = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5942  ->
                   match uu____5942 with
                   | (x,uu____5951) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5972  ->
      match uu____5972 with
      | (us',t) ->
          let n = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let uu____5996 = subst s t  in (us', uu____5996)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6015  ->
      match uu____6015 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6029 = subst s1 t  in (us, uu____6029)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6070  ->
              match uu____6070 with
              | (x,uu____6079) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  
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
      let uu____6106 = open_term [b] t  in
      match uu____6106 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6147 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6178 =
        let uu____6183 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6183 t  in
      match uu____6178 with
      | (bs,t1) ->
          let uu____6198 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6198, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6226 = open_term_bvs [bv] t  in
      match uu____6226 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6241 -> failwith "impossible: open_term_bv"
  