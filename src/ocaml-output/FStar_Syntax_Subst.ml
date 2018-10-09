open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____24 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____45  ->
              match uu____45 with
              | (b,uu____52) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____24 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____67 'Auu____68 .
    ('Auu____67 -> 'Auu____68 FStar_Pervasives_Native.option) ->
      'Auu____67 Prims.list ->
        ('Auu____67 Prims.list,'Auu____68) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____110 = f s0  in
          (match uu____110 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____143 'Auu____144 'Auu____145 .
    ('Auu____143 -> 'Auu____144 -> 'Auu____145) ->
      'Auu____145 ->
        ('Auu____143,'Auu____144) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____145
  =
  fun f  ->
    fun x  ->
      fun uu___95_172  ->
        match uu___95_172 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____208 'Auu____209 'Auu____210 .
    ('Auu____208 -> 'Auu____209 FStar_Pervasives_Native.option) ->
      'Auu____208 Prims.list ->
        ('Auu____208 Prims.list -> 'Auu____209 -> 'Auu____210) ->
          'Auu____210 -> 'Auu____210
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____258 = apply_until_some f s  in
          FStar_All.pipe_right uu____258 (map_some_curry g t)
  
let compose_subst :
  'Auu____284 .
    ('Auu____284 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____284 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____284 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
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
        | FStar_Syntax_Syntax.SomeUseRange uu____335 ->
            FStar_Pervasives_Native.snd s2
        | uu____338 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____421 ->
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
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____447;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____448;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____449;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____450;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____451;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____452;_},s)
        ->
        let uu____493 = FStar_Syntax_Unionfind.find uv  in
        (match uu____493 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____504 =
               let uu____507 =
                 let uu____515 = delay t' s  in force_uvar' uu____515  in
               FStar_Pervasives_Native.fst uu____507  in
             (uu____504, true)
         | uu____525 -> (t, false))
    | uu____532 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____554 = force_uvar' t  in
    match uu____554 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____590 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____590, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____664 = FStar_ST.op_Bang m  in
        (match uu____664 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____736 = try_read_memo_aux t'  in
             (match uu____736 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____818 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____835 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____835
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____861 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____861 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____865 -> u)
    | uu____868 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___96_890  ->
           match uu___96_890 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____898 =
                 let uu____899 =
                   let uu____900 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____900  in
                 FStar_Syntax_Syntax.bv_to_name uu____899  in
               FStar_Pervasives_Native.Some uu____898
           | uu____901 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___97_927  ->
           match uu___97_927 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____936 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___103_941 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___103_941.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___103_941.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____936
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____952 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___98_977  ->
           match uu___98_977 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____985 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___99_1006  ->
           match uu___99_1006 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____1014 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1042 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1052 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1052
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1056 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1056
  
let tag_with_range :
  'Auu____1066 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1066,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1092 =
            let uu____1094 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1095 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1094 uu____1095  in
          if uu____1092
          then t
          else
            (let r1 =
               let uu____1102 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1102
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1105 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1105
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1107 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1107
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___104_1113 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1114 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1114;
                       FStar_Syntax_Syntax.p =
                         (uu___104_1113.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___105_1116 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___105_1116.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___105_1116.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___106_1118 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___106_1118.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1128 .
    FStar_Ident.lident ->
      ('Auu____1128,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1148 =
            let uu____1150 =
              let uu____1151 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1151  in
            let uu____1152 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1150 uu____1152  in
          if uu____1148
          then l
          else
            (let uu____1156 =
               let uu____1157 = FStar_Ident.range_of_lid l  in
               let uu____1158 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1157 uu____1158  in
             FStar_Ident.set_lid_range l uu____1156)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1175 =
            let uu____1177 = FStar_Range.use_range r  in
            let uu____1178 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1177 uu____1178  in
          if uu____1175
          then r
          else
            (let uu____1182 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1182)
  
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
      | uu____1303 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1311 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1316 -> tag_with_range t0 s
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
               let uu____1385 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1386 =
                 let uu____1393 =
                   let uu____1394 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1394  in
                 FStar_Syntax_Syntax.mk uu____1393  in
               uu____1386 FStar_Pervasives_Native.None uu____1385
           | uu____1402 ->
               let uu____1403 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1403)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___100_1415  ->
              match uu___100_1415 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1419 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1419
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
      | uu____1447 ->
          let uu___107_1456 = t  in
          let uu____1457 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1462 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1467 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1470 =
            FStar_List.map
              (fun uu____1498  ->
                 match uu____1498 with
                 | (t1,imp) ->
                     let uu____1517 = subst' s t1  in
                     let uu____1518 = subst_imp' s imp  in
                     (uu____1517, uu____1518))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1523 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1457;
            FStar_Syntax_Syntax.effect_name = uu____1462;
            FStar_Syntax_Syntax.result_typ = uu____1467;
            FStar_Syntax_Syntax.effect_args = uu____1470;
            FStar_Syntax_Syntax.flags = uu____1523
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
      | uu____1554 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1575 = subst' s t1  in
               let uu____1576 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1575 uu____1576
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1593 = subst' s t1  in
               let uu____1594 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1593 uu____1594
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1602 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1602)

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
          let uu____1620 =
            let uu____1621 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1621  in
          FStar_Pervasives_Native.Some uu____1620
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
      | FStar_Syntax_Syntax.NT uu____1660 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1687 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1687)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1687)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1718 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1718, (FStar_Pervasives_Native.snd s))
  
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
    fun uu____1761  ->
      match uu____1761 with
      | (x,imp) ->
          let uu____1788 =
            let uu___108_1789 = x  in
            let uu____1790 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___108_1789.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___108_1789.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1790
            }  in
          let uu____1793 = subst_imp' s imp  in (uu____1788, uu____1793)
  
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
                  (let uu____1899 = shift_subst' i s  in
                   subst_binder' uu____1899 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1938 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1938) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1938)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1956  ->
      match uu____1956 with
      | (t,imp) -> let uu____1963 = subst' s t  in (uu____1963, imp)
  
let subst_args' :
  'Auu____1970 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1970) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1970)
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
        | FStar_Syntax_Syntax.Pat_constant uu____2064 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____2086 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2148  ->
                      fun uu____2149  ->
                        match (uu____2148, uu____2149) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2245 = aux n2 p2  in
                            (match uu____2245 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____2086 with
             | (pats1,n2) ->
                 ((let uu___109_2319 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___109_2319.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___110_2345 = x  in
              let uu____2346 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___110_2345.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___110_2345.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2346
              }  in
            ((let uu___111_2351 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___111_2351.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___112_2364 = x  in
              let uu____2365 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___112_2364.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___112_2364.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2365
              }  in
            ((let uu___113_2370 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___113_2370.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___114_2388 = x  in
              let uu____2389 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___114_2388.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___114_2388.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2389
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___115_2395 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___115_2395.FStar_Syntax_Syntax.p)
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
          let uu____2421 =
            let uu___116_2422 = rc  in
            let uu____2423 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___116_2422.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2423;
              FStar_Syntax_Syntax.residual_flags =
                (uu___116_2422.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2421
  
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
               (fun uu____2473  ->
                  match uu____2473 with
                  | (x',uu____2482) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___102_2498 =
          match uu___102_2498 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___101_2529  ->
                        match uu___101_2529 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2538 = should_retain x  in
                            if uu____2538
                            then
                              let uu____2543 =
                                let uu____2544 =
                                  let uu____2551 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2551)  in
                                FStar_Syntax_Syntax.NT uu____2544  in
                              [uu____2543]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2566 = should_retain x  in
                            if uu____2566
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___117_2574 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_2574.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___117_2574.FStar_Syntax_Syntax.sort)
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
                               | uu____2584 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2589 -> []))
                 in
              let uu____2590 = aux rest  in FStar_List.append hd1 uu____2590
           in
        let uu____2593 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2593 with
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
        let uu____2656 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2656  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2659 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2688 ->
               let t1 =
                 let uu____2698 =
                   let uu____2707 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2707  in
                 uu____2698 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2757 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2758 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2763 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2790 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2790 with
           | FStar_Pervasives_Native.None  ->
               let uu____2795 =
                 let uu___118_2798 = t  in
                 let uu____2801 =
                   let uu____2802 =
                     let uu____2815 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2815)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2802  in
                 {
                   FStar_Syntax_Syntax.n = uu____2801;
                   FStar_Syntax_Syntax.pos =
                     (uu___118_2798.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___118_2798.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2795 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2839 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2840 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2841 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2855 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2855 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2888 =
            let uu____2889 =
              let uu____2906 = subst' s t0  in
              let uu____2909 = subst_args' s args  in
              (uu____2906, uu____2909)  in
            FStar_Syntax_Syntax.Tm_app uu____2889  in
          mk1 uu____2888
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____3010 = subst' s t1  in FStar_Util.Inl uu____3010
            | FStar_Util.Inr c ->
                let uu____3024 = subst_comp' s c  in
                FStar_Util.Inr uu____3024
             in
          let uu____3031 =
            let uu____3032 =
              let uu____3059 = subst' s t0  in
              let uu____3062 =
                let uu____3079 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____3079)  in
              (uu____3059, uu____3062, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3032  in
          mk1 uu____3031
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____3165 =
            let uu____3166 =
              let uu____3185 = subst_binders' s bs  in
              let uu____3194 = subst' s' body  in
              let uu____3197 = push_subst_lcomp s' lopt  in
              (uu____3185, uu____3194, uu____3197)  in
            FStar_Syntax_Syntax.Tm_abs uu____3166  in
          mk1 uu____3165
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3241 =
            let uu____3242 =
              let uu____3257 = subst_binders' s bs  in
              let uu____3266 =
                let uu____3269 = shift_subst' n1 s  in
                subst_comp' uu____3269 comp  in
              (uu____3257, uu____3266)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3242  in
          mk1 uu____3241
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___119_3299 = x  in
            let uu____3300 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_3299.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_3299.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3300
            }  in
          let phi1 =
            let uu____3304 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3304 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3420  ->
                    match uu____3420 with
                    | (pat,wopt,branch) ->
                        let uu____3450 = subst_pat' s pat  in
                        (match uu____3450 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3481 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3481
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
                      let uu____3553 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3553
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___120_3571 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___120_3571.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___120_3571.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___121_3573 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___121_3573.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___121_3573.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___121_3573.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___121_3573.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3604 =
            let uu____3605 =
              let uu____3612 = subst' s t0  in
              let uu____3615 =
                let uu____3616 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3616  in
              (uu____3612, uu____3615)  in
            FStar_Syntax_Syntax.Tm_meta uu____3605  in
          mk1 uu____3604
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3682 =
            let uu____3683 =
              let uu____3690 = subst' s t0  in
              let uu____3693 =
                let uu____3694 =
                  let uu____3701 = subst' s t1  in (m, uu____3701)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3694  in
              (uu____3690, uu____3693)  in
            FStar_Syntax_Syntax.Tm_meta uu____3683  in
          mk1 uu____3682
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3720 =
            let uu____3721 =
              let uu____3728 = subst' s t0  in
              let uu____3731 =
                let uu____3732 =
                  let uu____3741 = subst' s t1  in (m1, m2, uu____3741)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3732  in
              (uu____3728, uu____3731)  in
            FStar_Syntax_Syntax.Tm_meta uu____3721  in
          mk1 uu____3720
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3756 =
                 let uu____3757 =
                   let uu____3764 = subst' s tm  in (uu____3764, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3757  in
               mk1 uu____3756
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3778 =
            let uu____3779 = let uu____3786 = subst' s t1  in (uu____3786, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3779  in
          mk1 uu____3778
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3800 = force_uvar t1  in
    match uu____3800 with
    | (t2,uu____3809) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3862 =
                 let uu____3867 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3867  in
               FStar_ST.op_Colon_Equals memo uu____3862);
              compress t2)
         | uu____3921 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3956 =
        let uu____3957 =
          let uu____3958 =
            let uu____3959 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3959  in
          FStar_Syntax_Syntax.SomeUseRange uu____3958  in
        ([], uu____3957)  in
      subst' uu____3956 t
  
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
    let uu____4020 =
      FStar_List.fold_right
        (fun uu____4047  ->
           fun uu____4048  ->
             match (uu____4047, uu____4048) with
             | ((x,uu____4083),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____4020 FStar_Pervasives_Native.fst
  
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
            let uu___122_4241 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4242 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4241.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4241.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4242
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4249 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4249
             in
          let uu____4255 = aux bs' o1  in
          (match uu____4255 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4316 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4316
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4354 = open_binders' bs  in
      match uu____4354 with
      | (bs',opening) ->
          let uu____4391 = subst opening t  in (bs', uu____4391, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4407 = open_term' bs t  in
      match uu____4407 with | (b,t1,uu____4420) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4436 = open_binders' bs  in
      match uu____4436 with
      | (bs',opening) ->
          let uu____4471 = subst_comp opening t  in (bs', uu____4471)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4521 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4546 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4617  ->
                    fun uu____4618  ->
                      match (uu____4617, uu____4618) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4732 = open_pat_aux sub2 p2  in
                          (match uu____4732 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4546 with
           | (pats1,sub2) ->
               ((let uu___123_4842 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___123_4842.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___124_4863 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4864 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___124_4863.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___124_4863.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4864
            }  in
          let sub2 =
            let uu____4870 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4870
             in
          ((let uu___125_4881 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___125_4881.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___126_4886 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4887 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_4886.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_4886.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4887
            }  in
          let sub2 =
            let uu____4893 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4893
             in
          ((let uu___127_4904 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___127_4904.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___128_4914 = x  in
            let uu____4915 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_4914.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_4914.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4915
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___129_4924 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___129_4924.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4938  ->
    match uu____4938 with
    | (p,wopt,e) ->
        let uu____4962 = open_pat p  in
        (match uu____4962 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4991 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4991
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____5011 = open_branch' br  in
    match uu____5011 with | (br1,uu____5017) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____5029 = closing_subst bs  in subst uu____5029 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____5043 = closing_subst bs  in subst_comp uu____5043 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___130_5111 = x  in
            let uu____5112 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_5111.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_5111.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5112
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____5119 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5119
             in
          let uu____5125 = aux s' tl1  in (x1, imp1) :: uu____5125
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
        (fun uu____5152  ->
           let uu____5153 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____5153)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____5207 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5232 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5303  ->
                    fun uu____5304  ->
                      match (uu____5303, uu____5304) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5418 = aux sub2 p2  in
                          (match uu____5418 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____5232 with
           | (pats1,sub2) ->
               ((let uu___131_5528 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___131_5528.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___132_5549 = x  in
            let uu____5550 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_5549.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_5549.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5550
            }  in
          let sub2 =
            let uu____5556 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5556
             in
          ((let uu___133_5567 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___133_5567.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___134_5572 = x  in
            let uu____5573 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_5572.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_5572.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5573
            }  in
          let sub2 =
            let uu____5579 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5579
             in
          ((let uu___135_5590 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___135_5590.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___136_5600 = x  in
            let uu____5601 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_5600.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_5600.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5601
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___137_5610 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___137_5610.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5620  ->
    match uu____5620 with
    | (p,wopt,e) ->
        let uu____5640 = close_pat p  in
        (match uu____5640 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5677 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5677
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
      let uu____5765 = univ_var_opening us  in
      match uu____5765 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5808 = univ_var_opening us  in
      match uu____5808 with
      | (s,us') -> let uu____5831 = subst_comp s c  in (us', uu____5831)
  
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
      let uu____5894 =
        let uu____5906 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5906
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5946  ->
                 match uu____5946 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5983 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5983  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___138_5991 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___138_5991.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___138_5991.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___138_5991.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___138_5991.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___138_5991.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___138_5991.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5894 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____6034 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6064  ->
                             match uu____6064 with
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
                    match uu____6034 with
                    | (uu____6113,us,u_let_rec_opening) ->
                        let uu___139_6126 = lb  in
                        let uu____6127 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6130 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___139_6126.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____6127;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___139_6126.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6130;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___139_6126.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___139_6126.FStar_Syntax_Syntax.lbpos)
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
      let uu____6157 =
        let uu____6165 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____6165
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____6194  ->
                 match uu____6194 with
                 | (i,out) ->
                     let uu____6217 =
                       let uu____6220 =
                         let uu____6221 =
                           let uu____6227 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____6227, i)  in
                         FStar_Syntax_Syntax.NM uu____6221  in
                       uu____6220 :: out  in
                     ((i + (Prims.parse_int "1")), uu____6217)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____6157 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____6266 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6286  ->
                             match uu____6286 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____6266 with
                    | (uu____6317,u_let_rec_closing) ->
                        let uu___140_6325 = lb  in
                        let uu____6326 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6329 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___140_6325.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___140_6325.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6326;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___140_6325.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6329;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___140_6325.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___140_6325.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____6345  ->
      match uu____6345 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6380  ->
                   match uu____6380 with
                   | (x,uu____6389) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6416  ->
      match uu____6416 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6446 = subst s t  in (us', uu____6446)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6465  ->
      match uu____6465 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6479 = subst s1 t  in (us, uu____6479)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6520  ->
              match uu____6520 with
              | (x,uu____6529) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6556 = open_term [b] t  in
      match uu____6556 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6597 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6628 =
        let uu____6633 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6633 t  in
      match uu____6628 with
      | (bs,t1) ->
          let uu____6648 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6648, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6676 = open_term_bvs [bv] t  in
      match uu____6676 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6691 -> failwith "impossible: open_term_bv"
  