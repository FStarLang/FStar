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
      fun uu___92_162  ->
        match uu___92_162 with
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
        let uu____476 = FStar_Syntax_Unionfind.find uv  in
        (match uu____476 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____486 =
               let uu____489 =
                 let uu____496 = delay t' s  in force_uvar' uu____496  in
               FStar_Pervasives_Native.fst uu____489  in
             (uu____486, true)
         | uu____503 -> (t, false))
    | uu____508 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____526 = force_uvar' t  in
    match uu____526 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____554 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____554, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____624 = FStar_ST.op_Bang m  in
        (match uu____624 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____693 = try_read_memo_aux t'  in
             (match uu____693 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____767 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____781 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____781
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____804 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____804 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____808 -> u)
    | uu____811 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___93_832  ->
           match uu___93_832 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____837 =
                 let uu____838 =
                   let uu____839 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____839  in
                 FStar_Syntax_Syntax.bv_to_name uu____838  in
               FStar_Pervasives_Native.Some uu____837
           | uu____840 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___94_865  ->
           match uu___94_865 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____872 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___100_877 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___100_877.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___100_877.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____872
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____888 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___95_910  ->
           match uu___95_910 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____915 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___96_935  ->
           match uu___96_935 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____940 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____966 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____976 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____976
      | FStar_Syntax_Syntax.U_max us ->
          let uu____980 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____980
  
let tag_with_range :
  'Auu____989 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____989,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1015 =
            let uu____1016 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1017 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1016 uu____1017  in
          if uu____1015
          then t
          else
            (let r1 =
               let uu____1022 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1022
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1025 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1025
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1027 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1027
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___101_1033 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1034 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1034;
                       FStar_Syntax_Syntax.p =
                         (uu___101_1033.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___102_1036 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___102_1036.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___102_1036.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___103_1038 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___103_1038.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1047 .
    FStar_Ident.lident ->
      ('Auu____1047,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1067 =
            let uu____1068 =
              let uu____1069 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1069  in
            let uu____1070 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1068 uu____1070  in
          if uu____1067
          then l
          else
            (let uu____1072 =
               let uu____1073 = FStar_Ident.range_of_lid l  in
               let uu____1074 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1073 uu____1074  in
             FStar_Ident.set_lid_range l uu____1072)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1090 =
            let uu____1091 = FStar_Range.use_range r  in
            let uu____1092 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1091 uu____1092  in
          if uu____1090
          then r
          else
            (let uu____1094 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1094)
  
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
      | uu____1214 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1222 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1227 -> tag_with_range t0 s
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
               let uu____1296 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1297 =
                 let uu____1304 =
                   let uu____1305 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1305  in
                 FStar_Syntax_Syntax.mk uu____1304  in
               uu____1297 FStar_Pervasives_Native.None uu____1296
           | uu____1313 ->
               let uu____1314 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1314)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___97_1326  ->
              match uu___97_1326 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1330 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1330
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
      | uu____1358 ->
          let uu___104_1367 = t  in
          let uu____1368 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1373 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1378 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1381 =
            FStar_List.map
              (fun uu____1409  ->
                 match uu____1409 with
                 | (t1,imp) ->
                     let uu____1428 = subst' s t1  in
                     let uu____1429 = subst_imp' s imp  in
                     (uu____1428, uu____1429))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1434 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1368;
            FStar_Syntax_Syntax.effect_name = uu____1373;
            FStar_Syntax_Syntax.result_typ = uu____1378;
            FStar_Syntax_Syntax.effect_args = uu____1381;
            FStar_Syntax_Syntax.flags = uu____1434
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
      | uu____1465 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1486 = subst' s t1  in
               let uu____1487 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1486 uu____1487
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1504 = subst' s t1  in
               let uu____1505 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1504 uu____1505
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1513 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1513)

and (subst_imp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1531 =
            let uu____1532 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1532  in
          FStar_Pervasives_Native.Some uu____1531
      | i1 -> i1

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
      | FStar_Syntax_Syntax.NT uu____1556 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1579 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1579)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1579)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1608 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1608, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    fun uu____1650  ->
      match uu____1650 with
      | (x,imp) ->
          let uu____1677 =
            let uu___105_1678 = x  in
            let uu____1679 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___105_1678.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___105_1678.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1679
            }  in
          let uu____1682 = subst_imp' s imp  in (uu____1677, uu____1682)
  
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
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
                  (let uu____1782 = shift_subst' i s  in
                   subst_binder' uu____1782 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1819 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1819) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1819)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1837  ->
      match uu____1837 with
      | (t,imp) -> let uu____1844 = subst' s t  in (uu____1844, imp)
  
let subst_args' :
  'Auu____1850 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1850) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1850)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1937 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1956 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2010  ->
                      fun uu____2011  ->
                        match (uu____2010, uu____2011) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2090 = aux n2 p2  in
                            (match uu____2090 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1956 with
             | (pats1,n2) ->
                 ((let uu___106_2146 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___106_2146.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___107_2170 = x  in
              let uu____2171 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___107_2170.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___107_2170.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2171
              }  in
            ((let uu___108_2175 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___108_2175.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___109_2187 = x  in
              let uu____2188 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___109_2187.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___109_2187.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2188
              }  in
            ((let uu___110_2192 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___110_2192.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___111_2209 = x  in
              let uu____2210 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___111_2209.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___111_2209.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2210
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___112_2215 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___112_2215.FStar_Syntax_Syntax.p)
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
          let uu____2239 =
            let uu___113_2240 = rc  in
            let uu____2241 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___113_2240.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2241;
              FStar_Syntax_Syntax.residual_flags =
                (uu___113_2240.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2239
  
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
               (fun uu____2288  ->
                  match uu____2288 with
                  | (x',uu____2296) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___99_2312 =
          match uu___99_2312 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___98_2343  ->
                        match uu___98_2343 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2352 = should_retain x  in
                            if uu____2352
                            then
                              let uu____2355 =
                                let uu____2356 =
                                  let uu____2363 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2363)  in
                                FStar_Syntax_Syntax.NT uu____2356  in
                              [uu____2355]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2375 = should_retain x  in
                            if uu____2375
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___114_2381 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___114_2381.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___114_2381.FStar_Syntax_Syntax.sort)
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
                               | uu____2390 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2394 -> []))
                 in
              let uu____2395 = aux rest  in FStar_List.append hd1 uu____2395
           in
        let uu____2398 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2398 with
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
        let uu____2460 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2460  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2463 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2491 ->
               let t1 =
                 let uu____2501 =
                   let uu____2510 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2510  in
                 uu____2501 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2560 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2561 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2566 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2593 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2593 with
           | FStar_Pervasives_Native.None  ->
               let uu____2598 =
                 let uu___115_2601 = t  in
                 let uu____2604 =
                   let uu____2605 =
                     let uu____2618 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2618)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2605  in
                 {
                   FStar_Syntax_Syntax.n = uu____2604;
                   FStar_Syntax_Syntax.pos =
                     (uu___115_2601.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_2601.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2598 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2642 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2643 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2644 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2658 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2658 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2691 =
            let uu____2692 =
              let uu____2709 = subst' s t0  in
              let uu____2712 = subst_args' s args  in
              (uu____2709, uu____2712)  in
            FStar_Syntax_Syntax.Tm_app uu____2692  in
          mk1 uu____2691
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2813 = subst' s t1  in FStar_Util.Inl uu____2813
            | FStar_Util.Inr c ->
                let uu____2827 = subst_comp' s c  in
                FStar_Util.Inr uu____2827
             in
          let uu____2834 =
            let uu____2835 =
              let uu____2862 = subst' s t0  in
              let uu____2865 =
                let uu____2882 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2882)  in
              (uu____2862, uu____2865, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2835  in
          mk1 uu____2834
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2968 =
            let uu____2969 =
              let uu____2988 = subst_binders' s bs  in
              let uu____2997 = subst' s' body  in
              let uu____3000 = push_subst_lcomp s' lopt  in
              (uu____2988, uu____2997, uu____3000)  in
            FStar_Syntax_Syntax.Tm_abs uu____2969  in
          mk1 uu____2968
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3044 =
            let uu____3045 =
              let uu____3060 = subst_binders' s bs  in
              let uu____3069 =
                let uu____3072 = shift_subst' n1 s  in
                subst_comp' uu____3072 comp  in
              (uu____3060, uu____3069)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3045  in
          mk1 uu____3044
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___116_3102 = x  in
            let uu____3103 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___116_3102.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___116_3102.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3103
            }  in
          let phi1 =
            let uu____3107 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3107 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3222  ->
                    match uu____3222 with
                    | (pat,wopt,branch) ->
                        let uu____3252 = subst_pat' s pat  in
                        (match uu____3252 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3280 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3280
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
                      let uu____3349 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3349
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___117_3364 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___117_3364.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___117_3364.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___118_3366 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___118_3366.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___118_3366.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___118_3366.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___118_3366.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3395 =
            let uu____3396 =
              let uu____3403 = subst' s t0  in
              let uu____3406 =
                let uu____3407 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3407  in
              (uu____3403, uu____3406)  in
            FStar_Syntax_Syntax.Tm_meta uu____3396  in
          mk1 uu____3395
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3473 =
            let uu____3474 =
              let uu____3481 = subst' s t0  in
              let uu____3484 =
                let uu____3485 =
                  let uu____3492 = subst' s t1  in (m, uu____3492)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3485  in
              (uu____3481, uu____3484)  in
            FStar_Syntax_Syntax.Tm_meta uu____3474  in
          mk1 uu____3473
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3511 =
            let uu____3512 =
              let uu____3519 = subst' s t0  in
              let uu____3522 =
                let uu____3523 =
                  let uu____3532 = subst' s t1  in (m1, m2, uu____3532)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3523  in
              (uu____3519, uu____3522)  in
            FStar_Syntax_Syntax.Tm_meta uu____3512  in
          mk1 uu____3511
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3547 =
                 let uu____3548 =
                   let uu____3555 = subst' s tm  in (uu____3555, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3548  in
               mk1 uu____3547
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3569 =
            let uu____3570 = let uu____3577 = subst' s t1  in (uu____3577, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3570  in
          mk1 uu____3569
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3590 = force_uvar t1  in
    match uu____3590 with
    | (t2,uu____3598) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3649 =
                 let uu____3654 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3654  in
               FStar_ST.op_Colon_Equals memo uu____3649);
              compress t2)
         | uu____3708 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3741 =
        let uu____3742 =
          let uu____3743 =
            let uu____3744 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3744  in
          FStar_Syntax_Syntax.SomeUseRange uu____3743  in
        ([], uu____3742)  in
      subst' uu____3741 t
  
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
    let uu____3802 =
      FStar_List.fold_right
        (fun uu____3827  ->
           fun uu____3828  ->
             match (uu____3827, uu____3828) with
             | ((x,uu____3860),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3802 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.subst_elt
                                                   Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___119_4007 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4008 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_4007.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_4007.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4008
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4015 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4015
             in
          let uu____4018 = aux bs' o1  in
          (match uu____4018 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4078 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4078
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4115 = open_binders' bs  in
      match uu____4115 with
      | (bs',opening) ->
          let uu____4152 = subst opening t  in (bs', uu____4152, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4167 = open_term' bs t  in
      match uu____4167 with | (b,t1,uu____4180) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4195 = open_binders' bs  in
      match uu____4195 with
      | (bs',opening) ->
          let uu____4230 = subst_comp opening t  in (bs', uu____4230)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4279 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4302 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4368  ->
                    fun uu____4369  ->
                      match (uu____4368, uu____4369) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4472 = open_pat_aux sub2 p2  in
                          (match uu____4472 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4302 with
           | (pats1,sub2) ->
               ((let uu___120_4574 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___120_4574.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___121_4593 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4594 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___121_4593.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___121_4593.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4594
            }  in
          let sub2 =
            let uu____4600 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4600
             in
          ((let uu___122_4608 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___122_4608.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___123_4613 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4614 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_4613.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_4613.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4614
            }  in
          let sub2 =
            let uu____4620 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4620
             in
          ((let uu___124_4628 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___124_4628.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___125_4638 = x  in
            let uu____4639 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___125_4638.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___125_4638.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4639
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___126_4648 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___126_4648.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4661  ->
    match uu____4661 with
    | (p,wopt,e) ->
        let uu____4685 = open_pat p  in
        (match uu____4685 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4714 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4714
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4733 = open_branch' br  in
    match uu____4733 with | (br1,uu____4739) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4750 = closing_subst bs  in subst uu____4750 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4763 = closing_subst bs  in subst_comp uu____4763 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___127_4830 = x  in
            let uu____4831 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_4830.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_4830.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4831
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4838 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4838
             in
          let uu____4841 = aux s' tl1  in (x1, imp1) :: uu____4841
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
        (fun uu____4867  ->
           let uu____4868 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4868)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4921 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4944 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5010  ->
                    fun uu____5011  ->
                      match (uu____5010, uu____5011) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5114 = aux sub2 p2  in
                          (match uu____5114 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4944 with
           | (pats1,sub2) ->
               ((let uu___128_5216 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_5216.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___129_5235 = x  in
            let uu____5236 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_5235.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_5235.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5236
            }  in
          let sub2 =
            let uu____5242 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5242
             in
          ((let uu___130_5250 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___130_5250.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___131_5255 = x  in
            let uu____5256 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_5255.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_5255.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5256
            }  in
          let sub2 =
            let uu____5262 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5262
             in
          ((let uu___132_5270 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___132_5270.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_5280 = x  in
            let uu____5281 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_5280.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_5280.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5281
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___134_5290 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_5290.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5299  ->
    match uu____5299 with
    | (p,wopt,e) ->
        let uu____5319 = close_pat p  in
        (match uu____5319 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5356 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5356
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
      let uu____5433 = univ_var_opening us  in
      match uu____5433 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5475 = univ_var_opening us  in
      match uu____5475 with
      | (s,us') -> let uu____5498 = subst_comp s c  in (us', uu____5498)
  
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
      let uu____5554 =
        let uu____5565 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5565
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5598  ->
                 match uu____5598 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5631 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5631  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___135_5637 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___135_5637.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___135_5637.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___135_5637.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___135_5637.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___135_5637.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___135_5637.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5554 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5675 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5703  ->
                             match uu____5703 with
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
                    match uu____5675 with
                    | (uu____5744,us,u_let_rec_opening) ->
                        let uu___136_5755 = lb  in
                        let uu____5756 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5759 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___136_5755.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5756;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___136_5755.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5759;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___136_5755.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___136_5755.FStar_Syntax_Syntax.lbpos)
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
      let uu____5785 =
        let uu____5792 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5792
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5814  ->
                 match uu____5814 with
                 | (i,out) ->
                     let uu____5833 =
                       let uu____5836 =
                         let uu____5837 =
                           let uu____5842 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5842, i)  in
                         FStar_Syntax_Syntax.NM uu____5837  in
                       uu____5836 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5833)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5785 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5874 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5892  ->
                             match uu____5892 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5874 with
                    | (uu____5915,u_let_rec_closing) ->
                        let uu___137_5921 = lb  in
                        let uu____5922 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5925 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___137_5921.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___137_5921.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5922;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___137_5921.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5925;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___137_5921.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___137_5921.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5940  ->
      match uu____5940 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5973  ->
                   match uu____5973 with
                   | (x,uu____5981) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6006  ->
      match uu____6006 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6032 = subst s t  in (us', uu____6032)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6050  ->
      match uu____6050 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6064 = subst s1 t  in (us, uu____6064)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6102  ->
              match uu____6102 with
              | (x,uu____6110) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6134 = open_term [b] t  in
      match uu____6134 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6175 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6204 =
        let uu____6209 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6209 t  in
      match uu____6204 with
      | (bs,t1) ->
          let uu____6224 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6224, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6251 = open_term_bvs [bv] t  in
      match uu____6251 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6266 -> failwith "impossible: open_term_bv"
  