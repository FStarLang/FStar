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
      fun uu___91_162  ->
        match uu___91_162 with
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
        (fun uu___92_832  ->
           match uu___92_832 with
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
        (fun uu___93_865  ->
           match uu___93_865 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____872 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___99_877 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_877.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___99_877.FStar_Syntax_Syntax.sort)
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
        (fun uu___94_910  ->
           match uu___94_910 with
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
        (fun uu___95_935  ->
           match uu___95_935 with
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
                     let uu___100_1033 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1034 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1034;
                       FStar_Syntax_Syntax.p =
                         (uu___100_1033.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___101_1036 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___101_1036.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___101_1036.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___102_1038 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___102_1038.FStar_Syntax_Syntax.vars)
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
      | uu____1206 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1214 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1219 -> tag_with_range t0 s
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
               let uu____1288 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1289 =
                 let uu____1296 =
                   let uu____1297 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1297  in
                 FStar_Syntax_Syntax.mk uu____1296  in
               uu____1289 FStar_Pervasives_Native.None uu____1288
           | uu____1305 ->
               let uu____1306 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1306)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___96_1318  ->
              match uu___96_1318 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1322 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1322
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
      | uu____1350 ->
          let uu___103_1359 = t  in
          let uu____1360 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1365 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1370 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1373 =
            FStar_List.map
              (fun uu____1400  ->
                 match uu____1400 with
                 | (t1,imp) ->
                     let uu____1419 = subst' s t1  in (uu____1419, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1422 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1360;
            FStar_Syntax_Syntax.effect_name = uu____1365;
            FStar_Syntax_Syntax.result_typ = uu____1370;
            FStar_Syntax_Syntax.effect_args = uu____1373;
            FStar_Syntax_Syntax.flags = uu____1422
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
      | uu____1453 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1474 = subst' s t1  in
               let uu____1475 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1474 uu____1475
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1492 = subst' s t1  in
               let uu____1493 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1492 uu____1493
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1501 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1501)

and (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1511 =
            let uu____1512 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1512  in
          FStar_Pervasives_Native.Some uu____1511
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
      | FStar_Syntax_Syntax.NT uu____1536 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1559 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1559)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1559)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1588 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1588, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    fun uu____1622  ->
      match uu____1622 with
      | (x,imp) ->
          let uu____1641 =
            let uu___104_1642 = x  in
            let uu____1643 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_1642.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_1642.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1643
            }  in
          let uu____1646 = subst_imp' s imp  in (uu____1641, uu____1646)
  
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
                  (let uu____1746 = shift_subst' i s  in
                   subst_binder' uu____1746 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1775 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1775) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1775)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1793  ->
      match uu____1793 with
      | (t,imp) -> let uu____1800 = subst' s t  in (uu____1800, imp)
  
let subst_args' :
  'Auu____1806 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1806) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1806)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1893 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1912 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1966  ->
                      fun uu____1967  ->
                        match (uu____1966, uu____1967) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2046 = aux n2 p2  in
                            (match uu____2046 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1912 with
             | (pats1,n2) ->
                 ((let uu___105_2102 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___105_2102.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___106_2126 = x  in
              let uu____2127 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___106_2126.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___106_2126.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2127
              }  in
            ((let uu___107_2131 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___107_2131.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___108_2143 = x  in
              let uu____2144 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___108_2143.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___108_2143.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2144
              }  in
            ((let uu___109_2148 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___109_2148.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___110_2165 = x  in
              let uu____2166 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___110_2165.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___110_2165.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2166
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___111_2171 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___111_2171.FStar_Syntax_Syntax.p)
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
          let uu____2195 =
            let uu___112_2196 = rc  in
            let uu____2197 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___112_2196.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2197;
              FStar_Syntax_Syntax.residual_flags =
                (uu___112_2196.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2195
  
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
               (fun uu____2244  ->
                  match uu____2244 with
                  | (x',uu____2252) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___98_2268 =
          match uu___98_2268 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___97_2299  ->
                        match uu___97_2299 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2308 = should_retain x  in
                            if uu____2308
                            then
                              let uu____2311 =
                                let uu____2312 =
                                  let uu____2319 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2319)  in
                                FStar_Syntax_Syntax.NT uu____2312  in
                              [uu____2311]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2331 = should_retain x  in
                            if uu____2331
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___113_2337 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___113_2337.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___113_2337.FStar_Syntax_Syntax.sort)
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
                               | uu____2346 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2350 -> []))
                 in
              let uu____2351 = aux rest  in FStar_List.append hd1 uu____2351
           in
        let uu____2354 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2354 with
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
        let uu____2416 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2416  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2419 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2447 ->
               let t1 =
                 let uu____2457 =
                   let uu____2466 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2466  in
                 uu____2457 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2516 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2517 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2522 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2549 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2549 with
           | FStar_Pervasives_Native.None  ->
               let uu____2554 =
                 let uu___114_2557 = t  in
                 let uu____2560 =
                   let uu____2561 =
                     let uu____2574 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2574)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2561  in
                 {
                   FStar_Syntax_Syntax.n = uu____2560;
                   FStar_Syntax_Syntax.pos =
                     (uu___114_2557.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_2557.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2554 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2598 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2599 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2600 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2614 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2614 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2647 =
            let uu____2648 =
              let uu____2665 = subst' s t0  in
              let uu____2668 = subst_args' s args  in
              (uu____2665, uu____2668)  in
            FStar_Syntax_Syntax.Tm_app uu____2648  in
          mk1 uu____2647
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2769 = subst' s t1  in FStar_Util.Inl uu____2769
            | FStar_Util.Inr c ->
                let uu____2783 = subst_comp' s c  in
                FStar_Util.Inr uu____2783
             in
          let uu____2790 =
            let uu____2791 =
              let uu____2818 = subst' s t0  in
              let uu____2821 =
                let uu____2838 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2838)  in
              (uu____2818, uu____2821, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2791  in
          mk1 uu____2790
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2924 =
            let uu____2925 =
              let uu____2944 = subst_binders' s bs  in
              let uu____2953 = subst' s' body  in
              let uu____2956 = push_subst_lcomp s' lopt  in
              (uu____2944, uu____2953, uu____2956)  in
            FStar_Syntax_Syntax.Tm_abs uu____2925  in
          mk1 uu____2924
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3000 =
            let uu____3001 =
              let uu____3016 = subst_binders' s bs  in
              let uu____3025 =
                let uu____3028 = shift_subst' n1 s  in
                subst_comp' uu____3028 comp  in
              (uu____3016, uu____3025)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3001  in
          mk1 uu____3000
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___115_3058 = x  in
            let uu____3059 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___115_3058.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___115_3058.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3059
            }  in
          let phi1 =
            let uu____3063 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3063 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3178  ->
                    match uu____3178 with
                    | (pat,wopt,branch) ->
                        let uu____3208 = subst_pat' s pat  in
                        (match uu____3208 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3236 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3236
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
                      let uu____3305 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3305
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___116_3320 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___116_3320.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___116_3320.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___117_3322 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___117_3322.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___117_3322.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___117_3322.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___117_3322.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3351 =
            let uu____3352 =
              let uu____3359 = subst' s t0  in
              let uu____3362 =
                let uu____3363 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3363  in
              (uu____3359, uu____3362)  in
            FStar_Syntax_Syntax.Tm_meta uu____3352  in
          mk1 uu____3351
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3429 =
            let uu____3430 =
              let uu____3437 = subst' s t0  in
              let uu____3440 =
                let uu____3441 =
                  let uu____3448 = subst' s t1  in (m, uu____3448)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3441  in
              (uu____3437, uu____3440)  in
            FStar_Syntax_Syntax.Tm_meta uu____3430  in
          mk1 uu____3429
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3467 =
            let uu____3468 =
              let uu____3475 = subst' s t0  in
              let uu____3478 =
                let uu____3479 =
                  let uu____3488 = subst' s t1  in (m1, m2, uu____3488)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3479  in
              (uu____3475, uu____3478)  in
            FStar_Syntax_Syntax.Tm_meta uu____3468  in
          mk1 uu____3467
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3503 =
                 let uu____3504 =
                   let uu____3511 = subst' s tm  in (uu____3511, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3504  in
               mk1 uu____3503
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3525 =
            let uu____3526 = let uu____3533 = subst' s t1  in (uu____3533, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3526  in
          mk1 uu____3525
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3546 = force_uvar t1  in
    match uu____3546 with
    | (t2,uu____3554) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3605 =
                 let uu____3610 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3610  in
               FStar_ST.op_Colon_Equals memo uu____3605);
              compress t2)
         | uu____3664 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3697 =
        let uu____3698 =
          let uu____3699 =
            let uu____3700 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3700  in
          FStar_Syntax_Syntax.SomeUseRange uu____3699  in
        ([], uu____3698)  in
      subst' uu____3697 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  -> fun imp  -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3764 =
      FStar_List.fold_right
        (fun uu____3789  ->
           fun uu____3790  ->
             match (uu____3789, uu____3790) with
             | ((x,uu____3822),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3764 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
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
            let uu___118_3997 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3998 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___118_3997.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___118_3997.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3998
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4007 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4007
             in
          let uu____4010 = aux bs' o1  in
          (match uu____4010 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4084 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4084
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4125 = open_binders' bs  in
      match uu____4125 with
      | (bs',opening) ->
          let uu____4168 = subst opening t  in (bs', uu____4168, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4183 = open_term' bs t  in
      match uu____4183 with | (b,t1,uu____4196) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4211 = open_binders' bs  in
      match uu____4211 with
      | (bs',opening) ->
          let uu____4252 = subst_comp opening t  in (bs', uu____4252)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4301 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4324 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4390  ->
                    fun uu____4391  ->
                      match (uu____4390, uu____4391) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4494 = open_pat_aux sub2 p2  in
                          (match uu____4494 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4324 with
           | (pats1,sub2) ->
               ((let uu___119_4596 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___119_4596.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___120_4615 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4616 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___120_4615.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___120_4615.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4616
            }  in
          let sub2 =
            let uu____4622 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4622
             in
          ((let uu___121_4630 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___121_4630.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___122_4635 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4636 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4635.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4635.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4636
            }  in
          let sub2 =
            let uu____4642 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4642
             in
          ((let uu___123_4650 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___123_4650.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___124_4660 = x  in
            let uu____4661 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___124_4660.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___124_4660.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4661
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___125_4670 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___125_4670.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4683  ->
    match uu____4683 with
    | (p,wopt,e) ->
        let uu____4707 = open_pat p  in
        (match uu____4707 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4736 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4736
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4755 = open_branch' br  in
    match uu____4755 with | (br1,uu____4761) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4772 = closing_subst bs  in subst uu____4772 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4785 = closing_subst bs  in subst_comp uu____4785 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___126_4858 = x  in
            let uu____4859 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_4858.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_4858.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4859
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4868 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4868
             in
          let uu____4871 = aux s' tl1  in (x1, imp1) :: uu____4871
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
        (fun uu____4903  ->
           let uu____4904 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4904)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4957 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4980 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5046  ->
                    fun uu____5047  ->
                      match (uu____5046, uu____5047) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5150 = aux sub2 p2  in
                          (match uu____5150 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4980 with
           | (pats1,sub2) ->
               ((let uu___127_5252 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___127_5252.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___128_5271 = x  in
            let uu____5272 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_5271.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_5271.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5272
            }  in
          let sub2 =
            let uu____5278 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5278
             in
          ((let uu___129_5286 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___129_5286.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___130_5291 = x  in
            let uu____5292 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_5291.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_5291.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5292
            }  in
          let sub2 =
            let uu____5298 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5298
             in
          ((let uu___131_5306 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___131_5306.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___132_5316 = x  in
            let uu____5317 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_5316.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_5316.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5317
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___133_5326 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___133_5326.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5335  ->
    match uu____5335 with
    | (p,wopt,e) ->
        let uu____5355 = close_pat p  in
        (match uu____5355 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5392 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5392
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
      let uu____5469 = univ_var_opening us  in
      match uu____5469 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5511 = univ_var_opening us  in
      match uu____5511 with
      | (s,us') -> let uu____5534 = subst_comp s c  in (us', uu____5534)
  
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
      let uu____5590 =
        let uu____5601 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5601
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5634  ->
                 match uu____5634 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5667 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5667  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___134_5673 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___134_5673.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___134_5673.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___134_5673.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___134_5673.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___134_5673.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___134_5673.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5590 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5711 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5739  ->
                             match uu____5739 with
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
                    match uu____5711 with
                    | (uu____5780,us,u_let_rec_opening) ->
                        let uu___135_5791 = lb  in
                        let uu____5792 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5795 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___135_5791.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5792;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___135_5791.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5795;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___135_5791.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___135_5791.FStar_Syntax_Syntax.lbpos)
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
      let uu____5821 =
        let uu____5828 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5828
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5850  ->
                 match uu____5850 with
                 | (i,out) ->
                     let uu____5869 =
                       let uu____5872 =
                         let uu____5873 =
                           let uu____5878 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5878, i)  in
                         FStar_Syntax_Syntax.NM uu____5873  in
                       uu____5872 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5869)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5821 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5910 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5928  ->
                             match uu____5928 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5910 with
                    | (uu____5951,u_let_rec_closing) ->
                        let uu___136_5957 = lb  in
                        let uu____5958 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5961 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___136_5957.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___136_5957.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5958;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___136_5957.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5961;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___136_5957.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___136_5957.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5976  ->
      match uu____5976 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6009  ->
                   match uu____6009 with
                   | (x,uu____6017) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6042  ->
      match uu____6042 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6068 = subst s t  in (us', uu____6068)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6086  ->
      match uu____6086 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6100 = subst s1 t  in (us, uu____6100)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6138  ->
              match uu____6138 with
              | (x,uu____6146) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6170 = open_term [b] t  in
      match uu____6170 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6211 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6240 =
        let uu____6245 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6245 t  in
      match uu____6240 with
      | (bs,t1) ->
          let uu____6260 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6260, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6287 = open_term_bvs [bv] t  in
      match uu____6287 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6302 -> failwith "impossible: open_term_bv"
  