open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____41  ->
              match uu____41 with
              | (b,uu____47) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____58 'Auu____59 .
    ('Auu____58 -> 'Auu____59 FStar_Pervasives_Native.option) ->
      'Auu____58 Prims.list ->
        ('Auu____58 Prims.list,'Auu____59) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____101 = f s0  in
          (match uu____101 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____133 'Auu____134 'Auu____135 .
    ('Auu____133 -> 'Auu____134 -> 'Auu____135) ->
      'Auu____135 ->
        ('Auu____133,'Auu____134) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____135
  =
  fun f  ->
    fun x  ->
      fun uu___89_162  ->
        match uu___89_162 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____197 'Auu____198 'Auu____199 .
    ('Auu____197 -> 'Auu____198 FStar_Pervasives_Native.option) ->
      'Auu____197 Prims.list ->
        ('Auu____197 Prims.list -> 'Auu____198 -> 'Auu____199) ->
          'Auu____199 -> 'Auu____199
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____247 = apply_until_some f s  in
          FStar_All.pipe_right uu____247 (map_some_curry g t)
  
let compose_subst :
  'Auu____272 .
    ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____323 ->
            FStar_Pervasives_Native.snd s2
        | uu____326 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____408 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____431;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____432;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____433;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____434;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____435;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____436;_},s)
        ->
        let uu____474 = FStar_Syntax_Unionfind.find uv  in
        (match uu____474 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____484 =
               let uu____487 =
                 let uu____494 = delay t' s  in force_uvar' uu____494  in
               FStar_Pervasives_Native.fst uu____487  in
             (uu____484, true)
         | uu____501 -> (t, false))
    | uu____506 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____524 = force_uvar' t  in
    match uu____524 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____552 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____552, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____622 = FStar_ST.op_Bang m  in
        (match uu____622 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____695 = try_read_memo_aux t'  in
             (match uu____695 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____773 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____787 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____787
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____810 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____810 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____814 -> u)
    | uu____817 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___90_838  ->
           match uu___90_838 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____843 =
                 let uu____844 =
                   let uu____845 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____845  in
                 FStar_Syntax_Syntax.bv_to_name uu____844  in
               FStar_Pervasives_Native.Some uu____843
           | uu____846 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___91_871  ->
           match uu___91_871 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____878 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___97_883 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___97_883.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___97_883.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____878
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____894 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___92_916  ->
           match uu___92_916 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____921 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___93_941  ->
           match uu___93_941 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____946 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____972 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____982 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____982
      | FStar_Syntax_Syntax.U_max us ->
          let uu____986 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____986
  
let tag_with_range :
  'Auu____995 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____995,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1021 =
            let uu____1022 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1023 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1022 uu____1023  in
          if uu____1021
          then t
          else
            (let r1 =
               let uu____1028 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1028
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1031 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1031
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1033 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1033
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___98_1039 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1040 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1040;
                       FStar_Syntax_Syntax.p =
                         (uu___98_1039.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___99_1042 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___99_1042.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___99_1042.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___100_1044 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___100_1044.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1053 .
    FStar_Ident.lident ->
      ('Auu____1053,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1073 =
            let uu____1074 =
              let uu____1075 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1075  in
            let uu____1076 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1074 uu____1076  in
          if uu____1073
          then l
          else
            (let uu____1078 =
               let uu____1079 = FStar_Ident.range_of_lid l  in
               let uu____1080 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1079 uu____1080  in
             FStar_Ident.set_lid_range l uu____1078)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1096 =
            let uu____1097 = FStar_Range.use_range r  in
            let uu____1098 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1097 uu____1098  in
          if uu____1096
          then r
          else
            (let uu____1100 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1100)
  
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
      | uu____1200 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1208 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1213 -> tag_with_range t0 s
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
               let uu____1282 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1283 =
                 let uu____1290 =
                   let uu____1291 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1291  in
                 FStar_Syntax_Syntax.mk uu____1290  in
               uu____1283 FStar_Pervasives_Native.None uu____1282
           | uu____1299 ->
               let uu____1300 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1300)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___94_1312  ->
              match uu___94_1312 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1316 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1316
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1344 ->
          let uu___101_1353 = t  in
          let uu____1354 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1359 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1364 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1367 =
            FStar_List.map
              (fun uu____1388  ->
                 match uu____1388 with
                 | (t1,imp) ->
                     let uu____1399 = subst' s t1  in (uu____1399, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1400 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1354;
            FStar_Syntax_Syntax.effect_name = uu____1359;
            FStar_Syntax_Syntax.result_typ = uu____1364;
            FStar_Syntax_Syntax.effect_args = uu____1367;
            FStar_Syntax_Syntax.flags = uu____1400
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1431 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1452 = subst' s t1  in
               let uu____1453 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1452 uu____1453
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1470 = subst' s t1  in
               let uu____1471 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1470 uu____1471
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1479 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1479)

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
      | FStar_Syntax_Syntax.NT uu____1498 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1521 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1521)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1521)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1550 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1550, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1569 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1569) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1569) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1587  ->
      match uu____1587 with
      | (x,imp) ->
          let uu____1594 =
            let uu___102_1595 = x  in
            let uu____1596 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___102_1595.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___102_1595.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1596
            }  in
          (uu____1594, imp)
  
let subst_binders' :
  'Auu____1605 .
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____1605) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1605) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1683 = shift_subst' i s  in
                   subst_binder' uu____1683 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1712 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1712) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1712)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1730  ->
      match uu____1730 with
      | (t,imp) -> let uu____1737 = subst' s t  in (uu____1737, imp)
  
let subst_args' :
  'Auu____1743 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1743) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1743)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1830 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1849 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1903  ->
                      fun uu____1904  ->
                        match (uu____1903, uu____1904) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1983 = aux n2 p2  in
                            (match uu____1983 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1849 with
             | (pats1,n2) ->
                 ((let uu___103_2039 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___103_2039.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___104_2063 = x  in
              let uu____2064 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___104_2063.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___104_2063.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2064
              }  in
            ((let uu___105_2068 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___105_2068.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___106_2080 = x  in
              let uu____2081 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___106_2080.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___106_2080.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2081
              }  in
            ((let uu___107_2085 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___107_2085.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___108_2102 = x  in
              let uu____2103 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___108_2102.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___108_2102.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2103
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___109_2108 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___109_2108.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
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
          let uu____2132 =
            let uu___110_2133 = rc  in
            let uu____2134 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___110_2133.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2134;
              FStar_Syntax_Syntax.residual_flags =
                (uu___110_2133.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2132
  
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
               (fun uu____2177  ->
                  match uu____2177 with
                  | (x',uu____2183) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___96_2195 =
          match uu___96_2195 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___95_2226  ->
                        match uu___95_2226 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2235 = should_retain x  in
                            if uu____2235
                            then
                              let uu____2238 =
                                let uu____2239 =
                                  let uu____2246 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2246)  in
                                FStar_Syntax_Syntax.NT uu____2239  in
                              [uu____2238]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2258 = should_retain x  in
                            if uu____2258
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___111_2264 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___111_2264.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___111_2264.FStar_Syntax_Syntax.sort)
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
                               | uu____2273 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2277 -> []))
                 in
              let uu____2278 = aux rest  in FStar_List.append hd1 uu____2278
           in
        let uu____2281 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2281 with
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
        let uu____2343 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2343  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2346 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2372 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2377 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2404 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2404 with
           | FStar_Pervasives_Native.None  ->
               let uu____2409 =
                 let uu___112_2412 = t  in
                 let uu____2415 =
                   let uu____2416 =
                     let uu____2429 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2429)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2416  in
                 {
                   FStar_Syntax_Syntax.n = uu____2415;
                   FStar_Syntax_Syntax.pos =
                     (uu___112_2412.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___112_2412.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2409 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2453 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2454 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2455 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2469 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2469 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2498 =
            let uu____2499 =
              let uu____2514 = subst' s t0  in
              let uu____2517 = subst_args' s args  in
              (uu____2514, uu____2517)  in
            FStar_Syntax_Syntax.Tm_app uu____2499  in
          mk1 uu____2498
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2612 = subst' s t1  in FStar_Util.Inl uu____2612
            | FStar_Util.Inr c ->
                let uu____2626 = subst_comp' s c  in
                FStar_Util.Inr uu____2626
             in
          let uu____2633 =
            let uu____2634 =
              let uu____2661 = subst' s t0  in
              let uu____2664 =
                let uu____2681 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2681)  in
              (uu____2661, uu____2664, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2634  in
          mk1 uu____2633
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2761 =
            let uu____2762 =
              let uu____2779 = subst_binders' s bs  in
              let uu____2786 = subst' s' body  in
              let uu____2789 = push_subst_lcomp s' lopt  in
              (uu____2779, uu____2786, uu____2789)  in
            FStar_Syntax_Syntax.Tm_abs uu____2762  in
          mk1 uu____2761
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2825 =
            let uu____2826 =
              let uu____2839 = subst_binders' s bs  in
              let uu____2846 =
                let uu____2849 = shift_subst' n1 s  in
                subst_comp' uu____2849 comp  in
              (uu____2839, uu____2846)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2826  in
          mk1 uu____2825
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___113_2877 = x  in
            let uu____2878 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___113_2877.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___113_2877.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2878
            }  in
          let phi1 =
            let uu____2882 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2882 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2997  ->
                    match uu____2997 with
                    | (pat,wopt,branch) ->
                        let uu____3027 = subst_pat' s pat  in
                        (match uu____3027 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3055 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3055
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
                      let uu____3124 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3124
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___114_3139 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___114_3139.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___114_3139.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___115_3141 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___115_3141.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___115_3141.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___115_3141.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___115_3141.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3168 =
            let uu____3169 =
              let uu____3176 = subst' s t0  in
              let uu____3179 =
                let uu____3180 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3180  in
              (uu____3176, uu____3179)  in
            FStar_Syntax_Syntax.Tm_meta uu____3169  in
          mk1 uu____3168
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3234 =
            let uu____3235 =
              let uu____3242 = subst' s t0  in
              let uu____3245 =
                let uu____3246 =
                  let uu____3253 = subst' s t1  in (m, uu____3253)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3246  in
              (uu____3242, uu____3245)  in
            FStar_Syntax_Syntax.Tm_meta uu____3235  in
          mk1 uu____3234
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3272 =
            let uu____3273 =
              let uu____3280 = subst' s t0  in
              let uu____3283 =
                let uu____3284 =
                  let uu____3293 = subst' s t1  in (m1, m2, uu____3293)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3284  in
              (uu____3280, uu____3283)  in
            FStar_Syntax_Syntax.Tm_meta uu____3273  in
          mk1 uu____3272
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3308 =
                 let uu____3309 =
                   let uu____3316 = subst' s tm  in (uu____3316, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3309  in
               mk1 uu____3308
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3330 =
            let uu____3331 = let uu____3338 = subst' s t1  in (uu____3338, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3331  in
          mk1 uu____3330
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3351 = force_uvar t1  in
    match uu____3351 with
    | (t2,uu____3359) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3410 =
                 let uu____3415 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3415  in
               FStar_ST.op_Colon_Equals memo uu____3410);
              compress t2)
         | uu____3473 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3506 =
        let uu____3507 =
          let uu____3508 =
            let uu____3509 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3509  in
          FStar_Syntax_Syntax.SomeUseRange uu____3508  in
        ([], uu____3507)  in
      subst' uu____3506 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3545 =
      FStar_List.fold_right
        (fun uu____3568  ->
           fun uu____3569  ->
             match (uu____3568, uu____3569) with
             | ((x,uu____3597),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3545 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3632 .
    (FStar_Syntax_Syntax.bv,'Auu____3632) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3632) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___116_3743 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3744 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___116_3743.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___116_3743.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3744
            }  in
          let o1 =
            let uu____3750 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3750
             in
          let uu____3753 = aux bs' o1  in
          (match uu____3753 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3813 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3813
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____3850 = open_binders' bs  in
      match uu____3850 with
      | (bs',opening) ->
          let uu____3887 = subst opening t  in (bs', uu____3887, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3902 = open_term' bs t  in
      match uu____3902 with | (b,t1,uu____3915) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3930 = open_binders' bs  in
      match uu____3930 with
      | (bs',opening) ->
          let uu____3965 = subst_comp opening t  in (bs', uu____3965)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4014 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4037 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4103  ->
                    fun uu____4104  ->
                      match (uu____4103, uu____4104) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4207 = open_pat_aux sub2 p2  in
                          (match uu____4207 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4037 with
           | (pats1,sub2) ->
               ((let uu___117_4309 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___117_4309.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___118_4328 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4329 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___118_4328.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___118_4328.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4329
            }  in
          let sub2 =
            let uu____4335 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4335
             in
          ((let uu___119_4343 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___119_4343.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___120_4348 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4349 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___120_4348.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___120_4348.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4349
            }  in
          let sub2 =
            let uu____4355 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4355
             in
          ((let uu___121_4363 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___121_4363.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___122_4373 = x  in
            let uu____4374 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4373.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4373.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4374
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___123_4383 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___123_4383.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4396  ->
    match uu____4396 with
    | (p,wopt,e) ->
        let uu____4420 = open_pat p  in
        (match uu____4420 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4449 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4449
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4468 = open_branch' br  in
    match uu____4468 with | (br1,uu____4474) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4485 = closing_subst bs  in subst uu____4485 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4498 = closing_subst bs  in subst_comp uu____4498 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___124_4555 = x  in
            let uu____4556 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___124_4555.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___124_4555.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4556
            }  in
          let s' =
            let uu____4562 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4562
             in
          let uu____4565 = aux s' tl1  in (x1, imp) :: uu____4565
       in
    aux [] bs
  
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4591  ->
           let uu____4592 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4592)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4645 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4668 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4734  ->
                    fun uu____4735  ->
                      match (uu____4734, uu____4735) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4838 = aux sub2 p2  in
                          (match uu____4838 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4668 with
           | (pats1,sub2) ->
               ((let uu___125_4940 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___125_4940.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___126_4959 = x  in
            let uu____4960 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_4959.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_4959.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4960
            }  in
          let sub2 =
            let uu____4966 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4966
             in
          ((let uu___127_4974 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___127_4974.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___128_4979 = x  in
            let uu____4980 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_4979.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_4979.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4980
            }  in
          let sub2 =
            let uu____4986 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4986
             in
          ((let uu___129_4994 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___129_4994.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___130_5004 = x  in
            let uu____5005 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_5004.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_5004.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5005
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___131_5014 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___131_5014.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5023  ->
    match uu____5023 with
    | (p,wopt,e) ->
        let uu____5043 = close_pat p  in
        (match uu____5043 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5080 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5080
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
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
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun t  ->
      let uu____5157 = univ_var_opening us  in
      match uu____5157 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5199 = univ_var_opening us  in
      match uu____5199 with
      | (s,us') -> let uu____5222 = subst_comp s c  in (us', uu____5222)
  
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
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5278 =
        let uu____5289 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5289
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5322  ->
                 match uu____5322 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5355 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5355  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___132_5361 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___132_5361.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___132_5361.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___132_5361.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___132_5361.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___132_5361.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___132_5361.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5278 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5399 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5427  ->
                             match uu____5427 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5399 with
                    | (uu____5468,us,u_let_rec_opening) ->
                        let uu___133_5479 = lb  in
                        let uu____5480 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5483 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___133_5479.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5480;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___133_5479.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5483;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___133_5479.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___133_5479.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5509 =
        let uu____5516 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5516
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5538  ->
                 match uu____5538 with
                 | (i,out) ->
                     let uu____5557 =
                       let uu____5560 =
                         let uu____5561 =
                           let uu____5566 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5566, i)  in
                         FStar_Syntax_Syntax.NM uu____5561  in
                       uu____5560 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5557)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5509 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5598 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5616  ->
                             match uu____5616 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5598 with
                    | (uu____5639,u_let_rec_closing) ->
                        let uu___134_5645 = lb  in
                        let uu____5646 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5649 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___134_5645.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___134_5645.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5646;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___134_5645.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5649;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___134_5645.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___134_5645.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5664  ->
      match uu____5664 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5693  ->
                   match uu____5693 with
                   | (x,uu____5699) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5720  ->
      match uu____5720 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5746 = subst s t  in (us', uu____5746)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5764  ->
      match uu____5764 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5778 = subst s1 t  in (us, uu____5778)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5810  ->
              match uu____5810 with
              | (x,uu____5816) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun b  ->
    fun t  ->
      let uu____5836 = open_term [b] t  in
      match uu____5836 with
      | (b1::[],t1) -> (b1, t1)
      | uu____5867 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____5896 =
        let uu____5901 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____5901 t  in
      match uu____5896 with
      | (bs,t1) ->
          let uu____5914 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____5914, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____5937 = open_term_bvs [bv] t  in
      match uu____5937 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____5952 -> failwith "impossible: open_term_bv"
  