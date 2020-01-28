open Prims
let subst_to_string :
  'Auu____4 . (FStar_Syntax_Syntax.bv * 'Auu____4) Prims.list -> Prims.string
  =
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
  'Auu____66 'Auu____67 .
    ('Auu____66 -> 'Auu____67 FStar_Pervasives_Native.option) ->
      'Auu____66 Prims.list ->
        ('Auu____66 Prims.list * 'Auu____67) FStar_Pervasives_Native.option
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
  'Auu____142 'Auu____143 'Auu____144 .
    ('Auu____142 -> 'Auu____143 -> 'Auu____144) ->
      'Auu____144 ->
        ('Auu____142 * 'Auu____143) FStar_Pervasives_Native.option ->
          'Auu____144
  =
  fun f  ->
    fun x  ->
      fun uu___0_171  ->
        match uu___0_171 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____207 'Auu____208 'Auu____209 .
    ('Auu____207 -> 'Auu____208 FStar_Pervasives_Native.option) ->
      'Auu____207 Prims.list ->
        ('Auu____207 Prims.list -> 'Auu____208 -> 'Auu____209) ->
          'Auu____209 -> 'Auu____209
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____257 = apply_until_some f s  in
          FStar_All.pipe_right uu____257 (map_some_curry g t)
  
let compose_subst :
  'Auu____283 .
    ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
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
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____420 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____446;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____447;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____448;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____449;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____450;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____451;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____452;_},s)
        ->
        let uu____501 = FStar_Syntax_Unionfind.find uv  in
        (match uu____501 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____512 =
               let uu____515 =
                 let uu____523 = delay t' s  in force_uvar' uu____523  in
               FStar_Pervasives_Native.fst uu____515  in
             (uu____512, true)
         | uu____533 -> (t, false))
    | uu____540 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____557 = force_uvar' t  in
    match uu____557 with
    | (t',forced) ->
        if forced
        then
          delay t'
            ([],
              (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos)))
        else t
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____648 = FStar_ST.op_Bang m  in
        (match uu____648 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____698 = try_read_memo_aux t'  in
             (match uu____698 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____758 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____775 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____775
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____801 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____801 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____805 -> u)
    | uu____808 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_830  ->
           match uu___1_830 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____838 =
                 let uu____839 =
                   let uu____840 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____840  in
                 FStar_Syntax_Syntax.bv_to_name uu____839  in
               FStar_Pervasives_Native.Some uu____838
           | uu____841 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_867  ->
           match uu___2_867 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____876 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___108_881 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___108_881.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___108_881.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____876
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____892 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_917  ->
           match uu___3_917 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____925 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_946  ->
           match uu___4_946 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____954 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____982 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____992 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____992
      | FStar_Syntax_Syntax.U_max us ->
          let uu____996 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____996
  
let tag_with_range :
  'Auu____1006 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1006 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1032 =
            let uu____1034 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1035 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1034 uu____1035  in
          if uu____1032
          then t
          else
            (let r1 =
               let uu____1042 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1042
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1045 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1045
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1047 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1047
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___160_1053 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1054 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1054;
                       FStar_Syntax_Syntax.p =
                         (uu___160_1053.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___163_1056 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___163_1056.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___163_1056.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___168_1058 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___168_1058.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1068 .
    FStar_Ident.lident ->
      ('Auu____1068 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1088 =
            let uu____1090 =
              let uu____1091 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1091  in
            let uu____1092 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1090 uu____1092  in
          if uu____1088
          then l
          else
            (let uu____1096 =
               let uu____1097 = FStar_Ident.range_of_lid l  in
               let uu____1098 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1097 uu____1098  in
             FStar_Ident.set_lid_range l uu____1096)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1115 =
            let uu____1117 = FStar_Range.use_range r  in
            let uu____1118 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1117 uu____1118  in
          if uu____1115
          then r
          else
            (let uu____1122 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1122)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1175 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1183 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1188 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1257 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1258 =
                 let uu____1265 =
                   let uu____1266 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1266  in
                 FStar_Syntax_Syntax.mk uu____1265  in
               uu____1258 FStar_Pervasives_Native.None uu____1257
           | uu____1271 ->
               let uu____1272 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1272)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1297  ->
              match uu___5_1297 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1301 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1301
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
          let uu____1327 =
            let uu____1328 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1328  in
          FStar_Pervasives_Native.Some uu____1327
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
      | uu____1375 ->
          let uu___235_1384 = t  in
          let uu____1385 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1390 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1395 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1398 =
            FStar_List.map
              (fun uu____1426  ->
                 match uu____1426 with
                 | (t1,imp) ->
                     let uu____1445 = subst' s t1  in
                     let uu____1446 = subst_imp' s imp  in
                     (uu____1445, uu____1446))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1451 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1385;
            FStar_Syntax_Syntax.effect_name = uu____1390;
            FStar_Syntax_Syntax.result_typ = uu____1395;
            FStar_Syntax_Syntax.effect_args = uu____1398;
            FStar_Syntax_Syntax.flags = uu____1451
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
      | uu____1503 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1524 = subst' s t1  in
               let uu____1525 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1524 uu____1525
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1542 = subst' s t1  in
               let uu____1543 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1542 uu____1543
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1551 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1551)
  
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1585 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1612 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1612) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1612)
  =
  fun n1  ->
    fun s  ->
      let uu____1643 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1643, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1678  ->
      match uu____1678 with
      | (x,imp) ->
          let uu____1697 =
            let uu___288_1698 = x  in
            let uu____1699 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___288_1698.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___288_1698.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1699
            }  in
          let uu____1702 = subst_imp' s imp  in (uu____1697, uu____1702)
  
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
                  (let uu____1808 = shift_subst' i s  in
                   subst_binder' uu____1808 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1839 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1839) ->
        (FStar_Syntax_Syntax.term * 'Auu____1839)
  =
  fun s  ->
    fun uu____1857  ->
      match uu____1857 with
      | (t,imp) -> let uu____1864 = subst' s t  in (uu____1864, imp)
  
let subst_args' :
  'Auu____1871 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1871) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1871) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1965 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1987 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2049  ->
                      fun uu____2050  ->
                        match (uu____2049, uu____2050) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2146 = aux n2 p2  in
                            (match uu____2146 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1987 with
             | (pats1,n2) ->
                 ((let uu___325_2220 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___325_2220.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___330_2246 = x  in
              let uu____2247 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___330_2246.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___330_2246.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2247
              }  in
            ((let uu___333_2252 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___333_2252.FStar_Syntax_Syntax.p)
              }), (n1 + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___338_2265 = x  in
              let uu____2266 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___338_2265.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___338_2265.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2266
              }  in
            ((let uu___341_2271 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___341_2271.FStar_Syntax_Syntax.p)
              }), (n1 + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___348_2289 = x  in
              let uu____2290 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___348_2289.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___348_2289.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2290
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___352_2296 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___352_2296.FStar_Syntax_Syntax.p)
              }), n1)
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
          let uu____2322 =
            let uu___359_2323 = rc  in
            let uu____2324 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___359_2323.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2324;
              FStar_Syntax_Syntax.residual_flags =
                (uu___359_2323.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2322
  
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
               (fun uu____2374  ->
                  match uu____2374 with
                  | (x',uu____2383) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2399 =
          match uu___7_2399 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2430  ->
                        match uu___6_2430 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2439 = should_retain x  in
                            if uu____2439
                            then
                              let uu____2444 =
                                let uu____2445 =
                                  let uu____2452 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2452)  in
                                FStar_Syntax_Syntax.NT uu____2445  in
                              [uu____2444]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2467 = should_retain x  in
                            if uu____2467
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___386_2475 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___386_2475.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___386_2475.FStar_Syntax_Syntax.sort)
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
                               | uu____2485 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2490 -> []))
                 in
              let uu____2491 = aux rest  in FStar_List.append hd1 uu____2491
           in
        let uu____2494 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2494 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2557 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2557  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2560 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2589 ->
               let t1 =
                 let uu____2599 =
                   let uu____2608 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2608  in
                 uu____2599 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2658 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2659 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2664 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2691 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2691 with
           | FStar_Pervasives_Native.None  ->
               let uu____2696 =
                 let uu___419_2699 = t  in
                 let uu____2702 =
                   let uu____2703 =
                     let uu____2716 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2716)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2703  in
                 {
                   FStar_Syntax_Syntax.n = uu____2702;
                   FStar_Syntax_Syntax.pos =
                     (uu___419_2699.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___419_2699.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2696 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2740 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2741 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2742 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2756 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2756 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2789 =
            let uu____2790 =
              let uu____2807 = subst' s t0  in
              let uu____2810 = subst_args' s args  in
              (uu____2807, uu____2810)  in
            FStar_Syntax_Syntax.Tm_app uu____2790  in
          mk1 uu____2789
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2911 = subst' s t1  in FStar_Util.Inl uu____2911
            | FStar_Util.Inr c ->
                let uu____2925 = subst_comp' s c  in
                FStar_Util.Inr uu____2925
             in
          let uu____2932 =
            let uu____2933 =
              let uu____2960 = subst' s t0  in
              let uu____2963 =
                let uu____2980 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2980)  in
              (uu____2960, uu____2963, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2933  in
          mk1 uu____2932
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____3062 =
            let uu____3063 =
              let uu____3082 = subst_binders' s bs  in
              let uu____3091 = subst' s' body  in
              let uu____3094 = push_subst_lcomp s' lopt  in
              (uu____3082, uu____3091, uu____3094)  in
            FStar_Syntax_Syntax.Tm_abs uu____3063  in
          mk1 uu____3062
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3138 =
            let uu____3139 =
              let uu____3154 = subst_binders' s bs  in
              let uu____3163 =
                let uu____3166 = shift_subst' n1 s  in
                subst_comp' uu____3166 comp  in
              (uu____3154, uu____3163)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3139  in
          mk1 uu____3138
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___466_3192 = x  in
            let uu____3193 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___466_3192.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___466_3192.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3193
            }  in
          let phi1 =
            let uu____3197 = shift_subst' Prims.int_one s  in
            subst' uu____3197 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3313  ->
                    match uu____3313 with
                    | (pat,wopt,branch) ->
                        let uu____3343 = subst_pat' s pat  in
                        (match uu____3343 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3374 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3374
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs  in
          let sn = shift_subst' n1 s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3443 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3443
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___504_3461 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_3461.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_3461.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___510_3472 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___510_3472.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___510_3472.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___510_3472.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3524 =
            let uu____3525 =
              let uu____3532 = subst' s t0  in
              let uu____3535 =
                let uu____3536 =
                  let uu____3557 = FStar_List.map (subst' s) bs  in
                  let uu____3566 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3557, uu____3566)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3536  in
              (uu____3532, uu____3535)  in
            FStar_Syntax_Syntax.Tm_meta uu____3525  in
          mk1 uu____3524
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3648 =
            let uu____3649 =
              let uu____3656 = subst' s t0  in
              let uu____3659 =
                let uu____3660 =
                  let uu____3667 = subst' s t1  in (m, uu____3667)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3660  in
              (uu____3656, uu____3659)  in
            FStar_Syntax_Syntax.Tm_meta uu____3649  in
          mk1 uu____3648
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3686 =
            let uu____3687 =
              let uu____3694 = subst' s t0  in
              let uu____3697 =
                let uu____3698 =
                  let uu____3707 = subst' s t1  in (m1, m2, uu____3707)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3698  in
              (uu____3694, uu____3697)  in
            FStar_Syntax_Syntax.Tm_meta uu____3687  in
          mk1 uu____3686
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3722 =
                 let uu____3723 =
                   let uu____3730 = subst' s tm  in (uu____3730, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3723  in
               mk1 uu____3722
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3744 =
            let uu____3745 = let uu____3752 = subst' s t1  in (uu____3752, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3745  in
          mk1 uu____3744
  
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = try_read_memo t  in
    let t2 = force_uvar t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
        ((let uu____3819 =
            let uu____3824 = push_subst s t'  in
            FStar_Pervasives_Native.Some uu____3824  in
          FStar_ST.op_Colon_Equals memo uu____3819);
         compress_slow t2)
    | uu____3856 -> t2
  
let (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3863,uu____3864) ->
        compress_slow t
    | FStar_Syntax_Syntax.Tm_uvar (uu____3901,uu____3902) -> compress_slow t
    | uu____3919 -> t
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3954 =
        let uu____3955 =
          let uu____3956 =
            let uu____3957 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3957  in
          FStar_Syntax_Syntax.SomeUseRange uu____3956  in
        ([], uu____3955)  in
      subst' uu____3954 t
  
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
    let uu____4018 =
      FStar_List.fold_right
        (fun uu____4045  ->
           fun uu____4046  ->
             match (uu____4045, uu____4046) with
             | ((x,uu____4081),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____4018 FStar_Pervasives_Native.fst
  
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
            let uu___592_4219 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4220 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___592_4219.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___592_4219.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4220
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4227 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4227  in
          let uu____4233 = aux bs' o1  in
          (match uu____4233 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4294 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4294
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____4316 = open_binders' bs  in
      match uu____4316 with
      | (bs',opening) ->
          let uu____4329 = subst opening t  in (bs', uu____4329, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4345 = open_term' bs t  in
      match uu____4345 with | (b,t1,uu____4358) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4374 = open_binders' bs  in
      match uu____4374 with
      | (bs',opening) ->
          let uu____4385 = subst_comp opening t  in (bs', uu____4385)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4435 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4460 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4531  ->
                    fun uu____4532  ->
                      match (uu____4531, uu____4532) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4646 = open_pat_aux sub2 p2  in
                          (match uu____4646 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4460 with
           | (pats1,sub2) ->
               ((let uu___639_4756 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___639_4756.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___643_4777 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4778 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___643_4777.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___643_4777.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4778
            }  in
          let sub2 =
            let uu____4784 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4784  in
          ((let uu___647_4795 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___647_4795.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___651_4800 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4801 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___651_4800.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___651_4800.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4801
            }  in
          let sub2 =
            let uu____4807 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4807  in
          ((let uu___655_4818 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___655_4818.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___661_4828 = x  in
            let uu____4829 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___661_4828.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___661_4828.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4829
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___665_4838 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___665_4838.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4852  ->
    match uu____4852 with
    | (p,wopt,e) ->
        let uu____4876 = open_pat p  in
        (match uu____4876 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4905 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4905
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4925 = open_branch' br  in
    match uu____4925 with | (br1,uu____4931) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4943 = closing_subst bs  in subst uu____4943 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4957 = closing_subst bs  in subst_comp uu____4957 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___697_5025 = x  in
            let uu____5026 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___697_5025.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___697_5025.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5026
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____5033 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5033  in
          let uu____5039 = aux s' tl1  in (x1, imp1) :: uu____5039
       in
    aux [] bs
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____5103 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5128 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5199  ->
                    fun uu____5200  ->
                      match (uu____5199, uu____5200) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5314 = aux sub2 p2  in
                          (match uu____5314 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____5128 with
           | (pats1,sub2) ->
               ((let uu___724_5424 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___724_5424.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___728_5445 = x  in
            let uu____5446 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___728_5445.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___728_5445.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5446
            }  in
          let sub2 =
            let uu____5452 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5452  in
          ((let uu___732_5463 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___732_5463.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___736_5468 = x  in
            let uu____5469 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___736_5468.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___736_5468.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5469
            }  in
          let sub2 =
            let uu____5475 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5475  in
          ((let uu___740_5486 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___740_5486.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___746_5496 = x  in
            let uu____5497 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___746_5496.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___746_5496.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5497
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___750_5506 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___750_5506.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5516  ->
    match uu____5516 with
    | (p,wopt,e) ->
        let uu____5536 = close_pat p  in
        (match uu____5536 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5573 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5573
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us  ->
    let n1 = (FStar_List.length us) - Prims.int_one  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - Prims.int_one  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____5661 = univ_var_opening us  in
      match uu____5661 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5704 = univ_var_opening us  in
      match uu____5704 with
      | (s,us') -> let uu____5727 = subst_comp s c  in (us', uu____5727)
  
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
      let n1 = (FStar_List.length us) - Prims.int_one  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5790 =
        let uu____5802 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5802
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5842  ->
                 match uu____5842 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5879 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5879  in
                     ((i + Prims.int_one),
                       ((let uu___802_5887 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___802_5887.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___802_5887.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___802_5887.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___802_5887.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___802_5887.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___802_5887.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5790 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5930 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5960  ->
                             match uu____5960 with
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
                    match uu____5930 with
                    | (uu____6009,us,u_let_rec_opening) ->
                        let uu___819_6022 = lb  in
                        let uu____6023 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6026 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___819_6022.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____6023;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___819_6022.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6026;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___819_6022.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___819_6022.FStar_Syntax_Syntax.lbpos)
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
      let uu____6053 =
        let uu____6061 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____6061
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____6090  ->
                 match uu____6090 with
                 | (i,out) ->
                     let uu____6113 =
                       let uu____6116 =
                         let uu____6117 =
                           let uu____6123 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____6123, i)  in
                         FStar_Syntax_Syntax.NM uu____6117  in
                       uu____6116 :: out  in
                     ((i + Prims.int_one), uu____6113)) lbs
            (Prims.int_zero, [])
         in
      match uu____6053 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____6162 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6182  ->
                             match uu____6182 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____6162 with
                    | (uu____6213,u_let_rec_closing) ->
                        let uu___841_6221 = lb  in
                        let uu____6222 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6225 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___841_6221.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___841_6221.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6222;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___841_6221.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6225;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___841_6221.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___841_6221.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____6241  ->
      match uu____6241 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6276  ->
                   match uu____6276 with
                   | (x,uu____6285) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6306  ->
      match uu____6306 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6330 = subst s t  in (us', uu____6330)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6349  ->
      match uu____6349 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6363 = subst s1 t  in (us, uu____6363)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6404  ->
              match uu____6404 with
              | (x,uu____6413) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6440 = open_term [b] t  in
      match uu____6440 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6481 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6512 =
        let uu____6517 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6517 t  in
      match uu____6512 with
      | (bs,t1) ->
          let uu____6532 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6532, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6560 = open_term_bvs [bv] t  in
      match uu____6560 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6575 -> failwith "impossible: open_term_bv"
  