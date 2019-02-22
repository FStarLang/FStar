open Prims
let subst_to_string :
  'Auu____5 . (FStar_Syntax_Syntax.bv * 'Auu____5) Prims.list -> Prims.string
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
        ('Auu____67 Prims.list * 'Auu____68) FStar_Pervasives_Native.option
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
        ('Auu____143 * 'Auu____144) FStar_Pervasives_Native.option ->
          'Auu____145
  =
  fun f  ->
    fun x  ->
      fun uu___19_172  ->
        match uu___19_172 with
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
    ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____284 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
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
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
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
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
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
           FStar_Syntax_Syntax.ctx_uvar_range = uu____452;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____453;_},s)
        ->
        let uu____502 = FStar_Syntax_Unionfind.find uv  in
        (match uu____502 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____513 =
               let uu____516 =
                 let uu____524 = delay t' s  in force_uvar' uu____524  in
               FStar_Pervasives_Native.fst uu____516  in
             (uu____513, true)
         | uu____534 -> (t, false))
    | uu____541 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____563 = force_uvar' t  in
    match uu____563 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____599 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____599, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____673 = FStar_ST.op_Bang m  in
        (match uu____673 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____745 = try_read_memo_aux t'  in
             (match uu____745 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____827 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____844 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____844
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____870 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____870 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____874 -> u)
    | uu____877 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___20_899  ->
           match uu___20_899 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____907 =
                 let uu____908 =
                   let uu____909 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____909  in
                 FStar_Syntax_Syntax.bv_to_name uu____908  in
               FStar_Pervasives_Native.Some uu____907
           | uu____910 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___21_936  ->
           match uu___21_936 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____945 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___27_950 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___27_950.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___27_950.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____945
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____961 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___22_986  ->
           match uu___22_986 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____994 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___23_1015  ->
           match uu___23_1015 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____1023 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1051 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1061 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1061
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1065 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1065
  
let tag_with_range :
  'Auu____1075 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1075 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1101 =
            let uu____1103 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1104 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1103 uu____1104  in
          if uu____1101
          then t
          else
            (let r1 =
               let uu____1111 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1111
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1114 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1114
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1116 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1116
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___28_1122 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1123 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1123;
                       FStar_Syntax_Syntax.p =
                         (uu___28_1122.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___29_1125 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___29_1125.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___29_1125.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___30_1127 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___30_1127.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1137 .
    FStar_Ident.lident ->
      ('Auu____1137 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1157 =
            let uu____1159 =
              let uu____1160 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1160  in
            let uu____1161 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1159 uu____1161  in
          if uu____1157
          then l
          else
            (let uu____1165 =
               let uu____1166 = FStar_Ident.range_of_lid l  in
               let uu____1167 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1166 uu____1167  in
             FStar_Ident.set_lid_range l uu____1165)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1184 =
            let uu____1186 = FStar_Range.use_range r  in
            let uu____1187 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1186 uu____1187  in
          if uu____1184
          then r
          else
            (let uu____1191 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1191)
  
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
      | uu____1312 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1320 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1325 -> tag_with_range t0 s
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
               let uu____1394 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1395 =
                 let uu____1402 =
                   let uu____1403 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1403  in
                 FStar_Syntax_Syntax.mk uu____1402  in
               uu____1395 FStar_Pervasives_Native.None uu____1394
           | uu____1411 ->
               let uu____1412 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1412)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___24_1424  ->
              match uu___24_1424 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1428 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1428
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1456 ->
          let uu___31_1465 = t  in
          let uu____1466 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1471 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1476 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1479 =
            FStar_List.map
              (fun uu____1507  ->
                 match uu____1507 with
                 | (t1,imp) ->
                     let uu____1526 = subst' s t1  in
                     let uu____1527 = subst_imp' s imp  in
                     (uu____1526, uu____1527))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1532 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1466;
            FStar_Syntax_Syntax.effect_name = uu____1471;
            FStar_Syntax_Syntax.result_typ = uu____1476;
            FStar_Syntax_Syntax.effect_args = uu____1479;
            FStar_Syntax_Syntax.flags = uu____1532
          }

and (subst_comp' :
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
      | uu____1563 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1584 = subst' s t1  in
               let uu____1585 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1584 uu____1585
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1602 = subst' s t1  in
               let uu____1603 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1602 uu____1603
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1611 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1611)

and (subst_imp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1629 =
            let uu____1630 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1630  in
          FStar_Pervasives_Native.Some uu____1629
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
      | FStar_Syntax_Syntax.NT uu____1669 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1696 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1696) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1696)
  =
  fun n1  ->
    fun s  ->
      let uu____1727 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1727, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1770  ->
      match uu____1770 with
      | (x,imp) ->
          let uu____1797 =
            let uu___32_1798 = x  in
            let uu____1799 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___32_1798.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___32_1798.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1799
            }  in
          let uu____1802 = subst_imp' s imp  in (uu____1797, uu____1802)
  
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
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1908 = shift_subst' i s  in
                   subst_binder' uu____1908 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1947 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1947) ->
        (FStar_Syntax_Syntax.term * 'Auu____1947)
  =
  fun s  ->
    fun uu____1965  ->
      match uu____1965 with
      | (t,imp) -> let uu____1972 = subst' s t  in (uu____1972, imp)
  
let subst_args' :
  'Auu____1979 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1979) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1979) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____2073 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____2095 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2157  ->
                      fun uu____2158  ->
                        match (uu____2157, uu____2158) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2254 = aux n2 p2  in
                            (match uu____2254 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____2095 with
             | (pats1,n2) ->
                 ((let uu___33_2328 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___33_2328.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___34_2354 = x  in
              let uu____2355 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___34_2354.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___34_2354.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2355
              }  in
            ((let uu___35_2360 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___35_2360.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___36_2373 = x  in
              let uu____2374 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___36_2373.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___36_2373.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2374
              }  in
            ((let uu___37_2379 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___37_2379.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___38_2397 = x  in
              let uu____2398 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___38_2397.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___38_2397.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2398
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___39_2404 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___39_2404.FStar_Syntax_Syntax.p)
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
          let uu____2430 =
            let uu___40_2431 = rc  in
            let uu____2432 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___40_2431.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2432;
              FStar_Syntax_Syntax.residual_flags =
                (uu___40_2431.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2430
  
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
               (fun uu____2482  ->
                  match uu____2482 with
                  | (x',uu____2491) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___26_2507 =
          match uu___26_2507 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___25_2538  ->
                        match uu___25_2538 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2547 = should_retain x  in
                            if uu____2547
                            then
                              let uu____2552 =
                                let uu____2553 =
                                  let uu____2560 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2560)  in
                                FStar_Syntax_Syntax.NT uu____2553  in
                              [uu____2552]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2575 = should_retain x  in
                            if uu____2575
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___41_2583 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___41_2583.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___41_2583.FStar_Syntax_Syntax.sort)
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
                               | uu____2593 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2598 -> []))
                 in
              let uu____2599 = aux rest  in FStar_List.append hd1 uu____2599
           in
        let uu____2602 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2602 with
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
        let uu____2665 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2665  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2668 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2697 ->
               let t1 =
                 let uu____2707 =
                   let uu____2716 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2716  in
                 uu____2707 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2766 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2767 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2772 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2799 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2799 with
           | FStar_Pervasives_Native.None  ->
               let uu____2804 =
                 let uu___42_2807 = t  in
                 let uu____2810 =
                   let uu____2811 =
                     let uu____2824 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2824)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2811  in
                 {
                   FStar_Syntax_Syntax.n = uu____2810;
                   FStar_Syntax_Syntax.pos =
                     (uu___42_2807.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___42_2807.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2804 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2848 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2849 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2850 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2864 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2864 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2897 =
            let uu____2898 =
              let uu____2915 = subst' s t0  in
              let uu____2918 = subst_args' s args  in
              (uu____2915, uu____2918)  in
            FStar_Syntax_Syntax.Tm_app uu____2898  in
          mk1 uu____2897
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____3019 = subst' s t1  in FStar_Util.Inl uu____3019
            | FStar_Util.Inr c ->
                let uu____3033 = subst_comp' s c  in
                FStar_Util.Inr uu____3033
             in
          let uu____3040 =
            let uu____3041 =
              let uu____3068 = subst' s t0  in
              let uu____3071 =
                let uu____3088 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____3088)  in
              (uu____3068, uu____3071, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3041  in
          mk1 uu____3040
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____3174 =
            let uu____3175 =
              let uu____3194 = subst_binders' s bs  in
              let uu____3203 = subst' s' body  in
              let uu____3206 = push_subst_lcomp s' lopt  in
              (uu____3194, uu____3203, uu____3206)  in
            FStar_Syntax_Syntax.Tm_abs uu____3175  in
          mk1 uu____3174
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3250 =
            let uu____3251 =
              let uu____3266 = subst_binders' s bs  in
              let uu____3275 =
                let uu____3278 = shift_subst' n1 s  in
                subst_comp' uu____3278 comp  in
              (uu____3266, uu____3275)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3251  in
          mk1 uu____3250
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___43_3308 = x  in
            let uu____3309 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___43_3308.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___43_3308.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3309
            }  in
          let phi1 =
            let uu____3313 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3313 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3429  ->
                    match uu____3429 with
                    | (pat,wopt,branch) ->
                        let uu____3459 = subst_pat' s pat  in
                        (match uu____3459 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3490 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3490
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
                      let uu____3562 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3562
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___44_3580 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___44_3580.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___44_3580.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___45_3582 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___45_3582.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___45_3582.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___45_3582.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___45_3582.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3613 =
            let uu____3614 =
              let uu____3621 = subst' s t0  in
              let uu____3624 =
                let uu____3625 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3625  in
              (uu____3621, uu____3624)  in
            FStar_Syntax_Syntax.Tm_meta uu____3614  in
          mk1 uu____3613
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3691 =
            let uu____3692 =
              let uu____3699 = subst' s t0  in
              let uu____3702 =
                let uu____3703 =
                  let uu____3710 = subst' s t1  in (m, uu____3710)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3703  in
              (uu____3699, uu____3702)  in
            FStar_Syntax_Syntax.Tm_meta uu____3692  in
          mk1 uu____3691
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3729 =
            let uu____3730 =
              let uu____3737 = subst' s t0  in
              let uu____3740 =
                let uu____3741 =
                  let uu____3750 = subst' s t1  in (m1, m2, uu____3750)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3741  in
              (uu____3737, uu____3740)  in
            FStar_Syntax_Syntax.Tm_meta uu____3730  in
          mk1 uu____3729
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3765 =
                 let uu____3766 =
                   let uu____3773 = subst' s tm  in (uu____3773, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3766  in
               mk1 uu____3765
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3787 =
            let uu____3788 = let uu____3795 = subst' s t1  in (uu____3795, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3788  in
          mk1 uu____3787
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3809 = force_uvar t1  in
    match uu____3809 with
    | (t2,uu____3818) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3871 =
                 let uu____3876 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3876  in
               FStar_ST.op_Colon_Equals memo uu____3871);
              compress t2)
         | uu____3930 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3965 =
        let uu____3966 =
          let uu____3967 =
            let uu____3968 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3968  in
          FStar_Syntax_Syntax.SomeUseRange uu____3967  in
        ([], uu____3966)  in
      subst' uu____3965 t
  
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
    let uu____4029 =
      FStar_List.fold_right
        (fun uu____4056  ->
           fun uu____4057  ->
             match (uu____4056, uu____4057) with
             | ((x,uu____4092),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____4029 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___46_4250 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4251 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___46_4250.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___46_4250.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4251
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4258 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4258
             in
          let uu____4264 = aux bs' o1  in
          (match uu____4264 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4325 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4325
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____4363 = open_binders' bs  in
      match uu____4363 with
      | (bs',opening) ->
          let uu____4400 = subst opening t  in (bs', uu____4400, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4416 = open_term' bs t  in
      match uu____4416 with | (b,t1,uu____4429) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4445 = open_binders' bs  in
      match uu____4445 with
      | (bs',opening) ->
          let uu____4480 = subst_comp opening t  in (bs', uu____4480)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4530 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4555 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4626  ->
                    fun uu____4627  ->
                      match (uu____4626, uu____4627) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4741 = open_pat_aux sub2 p2  in
                          (match uu____4741 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4555 with
           | (pats1,sub2) ->
               ((let uu___47_4851 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___47_4851.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___48_4872 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4873 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___48_4872.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___48_4872.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4873
            }  in
          let sub2 =
            let uu____4879 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4879
             in
          ((let uu___49_4890 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___49_4890.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___50_4895 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4896 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___50_4895.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___50_4895.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4896
            }  in
          let sub2 =
            let uu____4902 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4902
             in
          ((let uu___51_4913 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___51_4913.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___52_4923 = x  in
            let uu____4924 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___52_4923.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___52_4923.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4924
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___53_4933 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___53_4933.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4947  ->
    match uu____4947 with
    | (p,wopt,e) ->
        let uu____4971 = open_pat p  in
        (match uu____4971 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5000 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____5000
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____5020 = open_branch' br  in
    match uu____5020 with | (br1,uu____5026) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____5038 = closing_subst bs  in subst uu____5038 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____5052 = closing_subst bs  in subst_comp uu____5052 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___54_5120 = x  in
            let uu____5121 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___54_5120.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___54_5120.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5121
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____5128 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5128
             in
          let uu____5134 = aux s' tl1  in (x1, imp1) :: uu____5134
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
        (fun uu____5161  ->
           let uu____5162 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____5162)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____5216 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5241 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5312  ->
                    fun uu____5313  ->
                      match (uu____5312, uu____5313) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5427 = aux sub2 p2  in
                          (match uu____5427 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____5241 with
           | (pats1,sub2) ->
               ((let uu___55_5537 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___55_5537.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___56_5558 = x  in
            let uu____5559 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___56_5558.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___56_5558.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5559
            }  in
          let sub2 =
            let uu____5565 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5565
             in
          ((let uu___57_5576 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___57_5576.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___58_5581 = x  in
            let uu____5582 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___58_5581.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___58_5581.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5582
            }  in
          let sub2 =
            let uu____5588 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5588
             in
          ((let uu___59_5599 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___59_5599.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___60_5609 = x  in
            let uu____5610 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___60_5609.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___60_5609.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5610
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___61_5619 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___61_5619.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5629  ->
    match uu____5629 with
    | (p,wopt,e) ->
        let uu____5649 = close_pat p  in
        (match uu____5649 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5686 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5686
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
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
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____5774 = univ_var_opening us  in
      match uu____5774 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5817 = univ_var_opening us  in
      match uu____5817 with
      | (s,us') -> let uu____5840 = subst_comp s c  in (us', uu____5840)
  
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
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5903 =
        let uu____5915 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5915
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5955  ->
                 match uu____5955 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5992 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5992  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___62_6000 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___62_6000.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___62_6000.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___62_6000.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___62_6000.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___62_6000.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___62_6000.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5903 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____6043 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6073  ->
                             match uu____6073 with
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
                    match uu____6043 with
                    | (uu____6122,us,u_let_rec_opening) ->
                        let uu___63_6135 = lb  in
                        let uu____6136 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6139 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___63_6135.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____6136;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___63_6135.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6139;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___63_6135.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___63_6135.FStar_Syntax_Syntax.lbpos)
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
      let uu____6166 =
        let uu____6174 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____6174
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____6203  ->
                 match uu____6203 with
                 | (i,out) ->
                     let uu____6226 =
                       let uu____6229 =
                         let uu____6230 =
                           let uu____6236 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____6236, i)  in
                         FStar_Syntax_Syntax.NM uu____6230  in
                       uu____6229 :: out  in
                     ((i + (Prims.parse_int "1")), uu____6226)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____6166 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____6275 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6295  ->
                             match uu____6295 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____6275 with
                    | (uu____6326,u_let_rec_closing) ->
                        let uu___64_6334 = lb  in
                        let uu____6335 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6338 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___64_6334.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___64_6334.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6335;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___64_6334.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6338;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___64_6334.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___64_6334.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____6354  ->
      match uu____6354 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6389  ->
                   match uu____6389 with
                   | (x,uu____6398) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6425  ->
      match uu____6425 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6455 = subst s t  in (us', uu____6455)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6474  ->
      match uu____6474 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6488 = subst s1 t  in (us, uu____6488)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6529  ->
              match uu____6529 with
              | (x,uu____6538) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6565 = open_term [b] t  in
      match uu____6565 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6606 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6637 =
        let uu____6642 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6642 t  in
      match uu____6637 with
      | (bs,t1) ->
          let uu____6657 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6657, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6685 = open_term_bvs [bv] t  in
      match uu____6685 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6700 -> failwith "impossible: open_term_bv"
  