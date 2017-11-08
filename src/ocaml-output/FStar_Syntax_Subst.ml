open Prims
let subst_to_string:
  'Auu____3 .
    (FStar_Syntax_Syntax.bv,'Auu____3) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____20 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____38  ->
              match uu____38 with
              | (b,uu____44) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
    FStar_All.pipe_right uu____20 (FStar_String.concat ", ")
let rec apply_until_some:
  'Auu____51 'Auu____52 .
    ('Auu____52 -> 'Auu____51 FStar_Pervasives_Native.option) ->
      'Auu____52 Prims.list ->
        ('Auu____52 Prims.list,'Auu____51) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____92 = f s0 in
          (match uu____92 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry:
  'Auu____118 'Auu____119 'Auu____120 .
    ('Auu____120 -> 'Auu____119 -> 'Auu____118) ->
      'Auu____118 ->
        ('Auu____120,'Auu____119) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____118
  =
  fun f  ->
    fun x  ->
      fun uu___150_144  ->
        match uu___150_144 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map:
  'Auu____172 'Auu____173 'Auu____174 .
    ('Auu____174 -> 'Auu____173 FStar_Pervasives_Native.option) ->
      'Auu____174 Prims.list ->
        ('Auu____174 Prims.list -> 'Auu____173 -> 'Auu____172) ->
          'Auu____172 -> 'Auu____172
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____218 = apply_until_some f s in
          FStar_All.pipe_right uu____218 (map_some_curry g t)
let compose_subst:
  'Auu____241 'Auu____242 .
    ('Auu____242 Prims.list,'Auu____241 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____242 Prims.list,'Auu____241 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____242 Prims.list,'Auu____241 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____311 ->
            FStar_Pervasives_Native.snd s2
        | uu____316 -> FStar_Pervasives_Native.snd s1 in
      (s, ropt)
let delay:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____422 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____447) ->
        let uu____472 = FStar_Syntax_Unionfind.find uv in
        (match uu____472 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____478 -> t)
    | uu____481 -> t
let force_uvar:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____494 = FStar_Util.physical_equality t t' in
    if uu____494
    then t
    else
      delay t'
        ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
let rec force_delayed_thunk:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____561 = FStar_ST.op_Bang m in
        (match uu____561 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____717 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____730 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____730 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____734 -> u)
    | uu____737 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___151_754  ->
           match uu___151_754 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____759 =
                 let uu____760 =
                   let uu____761 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____761 in
                 FStar_Syntax_Syntax.bv_to_name uu____760 in
               FStar_Pervasives_Native.Some uu____759
           | uu____762 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___152_779  ->
           match uu___152_779 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____784 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___156_787 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___156_787.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___156_787.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____784
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____796 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___153_812  ->
           match uu___153_812 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____817 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___154_833  ->
           match uu___154_833 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____838 -> FStar_Pervasives_Native.None)
let rec subst_univ:
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____860 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____870 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____870
      | FStar_Syntax_Syntax.U_max us ->
          let uu____874 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____874
let tag_with_range:
  'Auu____880 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____880,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____911 = FStar_Range.use_range r in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____911 in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____914 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____914
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____916 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____916
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___157_922 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___157_922.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___158_924 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___158_924.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___158_924.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___159_926 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___159_926.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range:
  'Auu____932 .
    FStar_Ident.lident ->
      ('Auu____932,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____956 =
            let uu____957 = FStar_Range.use_range r in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____957 in
          FStar_Ident.set_lid_range l uu____956
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____971 = FStar_Range.use_range r' in
          FStar_Range.set_use_range r uu____971
let rec subst':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1074 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1084 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1089 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1094 -> tag_with_range t0 s
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
               let uu____1203 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1204 =
                 let uu____1207 =
                   let uu____1208 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1208 in
                 FStar_Syntax_Syntax.mk uu____1207 in
               uu____1204 FStar_Pervasives_Native.None uu____1203
           | uu____1218 ->
               let uu____1219 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1219)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___155_1233  ->
              match uu___155_1233 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1237 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1237
              | f -> f))
and subst_comp_typ':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1271 ->
          let uu___160_1282 = t in
          let uu____1283 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1290 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1295 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1298 =
            FStar_List.map
              (fun uu____1323  ->
                 match uu____1323 with
                 | (t1,imp) ->
                     let uu____1342 = subst' s t1 in (uu____1342, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1347 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1283;
            FStar_Syntax_Syntax.effect_name = uu____1290;
            FStar_Syntax_Syntax.result_typ = uu____1295;
            FStar_Syntax_Syntax.effect_args = uu____1298;
            FStar_Syntax_Syntax.flags = uu____1347
          }
and subst_comp':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1384 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1407 = subst' s t1 in
               let uu____1408 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1407 uu____1408
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1427 = subst' s t1 in
               let uu____1428 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1427 uu____1428
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1438 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1438)
let shift:
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1453 -> s
let shift_subst:
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst':
  'Auu____1469 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1469)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1469)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1496 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1496, (FStar_Pervasives_Native.snd s))
let subst_binder':
  'Auu____1512 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1512) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1512) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1528  ->
      match uu____1528 with
      | (x,imp) ->
          let uu____1535 =
            let uu___161_1536 = x in
            let uu____1537 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___161_1536.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___161_1536.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1537
            } in
          (uu____1535, imp)
let subst_binders':
  'Auu____1543 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1543) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1543) FStar_Pervasives_Native.tuple2
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
                  (let uu____1603 = shift_subst' i s in
                   subst_binder' uu____1603 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg':
  'Auu____1629 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1629)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1629)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1649  ->
      match uu____1649 with
      | (t,imp) -> let uu____1662 = subst' s t in (uu____1662, imp)
let subst_args':
  'Auu____1669 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1669)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1669)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1757 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1778 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1832  ->
                      fun uu____1833  ->
                        match (uu____1832, uu____1833) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1912 = aux n2 p2 in
                            (match uu____1912 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1778 with
             | (pats1,n2) ->
                 ((let uu___162_1970 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___162_1970.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___163_1996 = x in
              let uu____1997 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___163_1996.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___163_1996.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1997
              } in
            ((let uu___164_2003 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___164_2003.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___165_2019 = x in
              let uu____2020 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___165_2019.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___165_2019.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2020
              } in
            ((let uu___166_2026 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___166_2026.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___167_2047 = x in
              let uu____2048 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___167_2047.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___167_2047.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2048
              } in
            let t01 = subst' s1 t0 in
            ((let uu___168_2057 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___168_2057.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2077 =
            let uu___169_2078 = rc in
            let uu____2079 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___169_2078.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2079;
              FStar_Syntax_Syntax.residual_flags =
                (uu___169_2078.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2077
let push_subst:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2106 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2106 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2109 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2136 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2141 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2150 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2171 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2172 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2173 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2189 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2189 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2218 =
            let uu____2219 =
              let uu____2234 = subst' s t0 in
              let uu____2237 = subst_args' s args in (uu____2234, uu____2237) in
            FStar_Syntax_Syntax.Tm_app uu____2219 in
          mk1 uu____2218
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2332 = subst' s t1 in FStar_Util.Inl uu____2332
            | FStar_Util.Inr c ->
                let uu____2346 = subst_comp' s c in FStar_Util.Inr uu____2346 in
          let uu____2353 =
            let uu____2354 =
              let uu____2381 = subst' s t0 in
              let uu____2384 =
                let uu____2401 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2401) in
              (uu____2381, uu____2384, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2354 in
          mk1 uu____2353
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2485 =
            let uu____2486 =
              let uu____2503 = subst_binders' s bs in
              let uu____2510 = subst' s' body in
              let uu____2513 = push_subst_lcomp s' lopt in
              (uu____2503, uu____2510, uu____2513) in
            FStar_Syntax_Syntax.Tm_abs uu____2486 in
          mk1 uu____2485
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2549 =
            let uu____2550 =
              let uu____2563 = subst_binders' s bs in
              let uu____2570 =
                let uu____2573 = shift_subst' n1 s in
                subst_comp' uu____2573 comp in
              (uu____2563, uu____2570) in
            FStar_Syntax_Syntax.Tm_arrow uu____2550 in
          mk1 uu____2549
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___170_2605 = x in
            let uu____2606 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___170_2605.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___170_2605.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2606
            } in
          let phi1 =
            let uu____2612 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2612 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2739  ->
                    match uu____2739 with
                    | (pat,wopt,branch) ->
                        let uu____2785 = subst_pat' s pat in
                        (match uu____2785 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2833 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2833 in
                             let branch1 = subst' s1 branch in
                             (pat1, wopt1, branch1)))) in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs in
          let sn = shift_subst' n1 s in
          let body1 = subst' sn body in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp in
                    let lbd =
                      let uu____2918 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2918
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___171_2933 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___171_2933.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___171_2933.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___172_2935 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___172_2935.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___172_2935.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2962 =
            let uu____2963 =
              let uu____2970 = subst' s t0 in
              let uu____2973 =
                let uu____2974 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2974 in
              (uu____2970, uu____2973) in
            FStar_Syntax_Syntax.Tm_meta uu____2963 in
          mk1 uu____2962
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3034 =
            let uu____3035 =
              let uu____3042 = subst' s t0 in
              let uu____3045 =
                let uu____3046 =
                  let uu____3053 = subst' s t1 in (m, uu____3053) in
                FStar_Syntax_Syntax.Meta_monadic uu____3046 in
              (uu____3042, uu____3045) in
            FStar_Syntax_Syntax.Tm_meta uu____3035 in
          mk1 uu____3034
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3072 =
            let uu____3073 =
              let uu____3080 = subst' s t0 in
              let uu____3083 =
                let uu____3084 =
                  let uu____3093 = subst' s t1 in (m1, m2, uu____3093) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3084 in
              (uu____3080, uu____3083) in
            FStar_Syntax_Syntax.Tm_meta uu____3073 in
          mk1 uu____3072
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3106 =
            let uu____3107 = let uu____3114 = subst' s t1 in (uu____3114, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3107 in
          mk1 uu____3106
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3177 = push_subst s t2 in compress uu____3177 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3197 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3201 -> compress t'
         | uu____3226 -> t')
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let set_use_range:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      let uu____3253 =
        let uu____3254 =
          let uu____3257 =
            let uu____3258 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu____3258 in
          FStar_Pervasives_Native.Some uu____3257 in
        ([], uu____3254) in
      subst' uu____3253 t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3292 =
      FStar_List.fold_right
        (fun uu____3315  ->
           fun uu____3316  ->
             match (uu____3315, uu____3316) with
             | ((x,uu____3344),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3292 FStar_Pervasives_Native.fst
let open_binders':
  'Auu____3377 .
    (FStar_Syntax_Syntax.bv,'Auu____3377) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3377) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___173_3483 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3484 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___173_3483.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___173_3483.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3484
            } in
          let o1 =
            let uu____3490 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3490 in
          let uu____3493 = aux bs' o1 in
          (match uu____3493 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let open_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3551 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3551
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3584 = open_binders' bs in
      match uu____3584 with
      | (bs',opening) ->
          let uu____3621 = subst opening t in (bs', uu____3621, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3640 = open_term' bs t in
      match uu____3640 with | (b,t1,uu____3653) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3664 = open_binders' bs in
      match uu____3664 with
      | (bs',opening) ->
          let uu____3699 = subst_comp opening t in (bs', uu____3699)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3779 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3808 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3900  ->
                    fun uu____3901  ->
                      match (uu____3900, uu____3901) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4049 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4049 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3808 with
           | (pats1,sub2,renaming1) ->
               ((let uu___174_4219 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___174_4219.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___175_4238 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4239 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___175_4238.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___175_4238.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4239
            } in
          let sub2 =
            let uu____4245 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4245 in
          ((let uu___176_4259 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___176_4259.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___177_4268 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4269 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___177_4268.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___177_4268.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4269
            } in
          let sub2 =
            let uu____4275 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4275 in
          ((let uu___178_4289 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___178_4289.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___179_4303 = x in
            let uu____4304 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___179_4303.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___179_4303.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4304
            } in
          let t01 = subst sub1 t0 in
          ((let uu___180_4319 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___180_4319.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4322 = open_pat_aux [] [] p in
    match uu____4322 with | (p1,sub1,uu____4349) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4376  ->
    match uu____4376 with
    | (p,wopt,e) ->
        let uu____4396 = open_pat p in
        (match uu____4396 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4415 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4415 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4425 = closing_subst bs in subst uu____4425 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4434 = closing_subst bs in subst_comp uu____4434 c
let close_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___181_4485 = x in
            let uu____4486 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___181_4485.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___181_4485.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4486
            } in
          let s' =
            let uu____4492 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4492 in
          let uu____4495 = aux s' tl1 in (x1, imp) :: uu____4495 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___182_4515 = lc in
      let uu____4516 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___182_4515.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4516;
        FStar_Syntax_Syntax.cflags =
          (uu___182_4515.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4521  ->
             let uu____4522 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____4522)
      }
let close_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4569 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4592 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4658  ->
                    fun uu____4659  ->
                      match (uu____4658, uu____4659) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4762 = aux sub2 p2 in
                          (match uu____4762 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4592 with
           | (pats1,sub2) ->
               ((let uu___183_4864 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___183_4864.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___184_4883 = x in
            let uu____4884 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___184_4883.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___184_4883.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4884
            } in
          let sub2 =
            let uu____4890 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4890 in
          ((let uu___185_4898 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___185_4898.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___186_4903 = x in
            let uu____4904 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___186_4903.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___186_4903.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4904
            } in
          let sub2 =
            let uu____4910 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4910 in
          ((let uu___187_4918 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___187_4918.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___188_4928 = x in
            let uu____4929 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___188_4928.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___188_4928.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4929
            } in
          let t01 = subst sub1 t0 in
          ((let uu___189_4938 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___189_4938.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4943  ->
    match uu____4943 with
    | (p,wopt,e) ->
        let uu____4963 = close_pat p in
        (match uu____4963 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4994 = subst closing w in
                   FStar_Pervasives_Native.Some uu____4994 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u)))) in
    (s, us)
let univ_var_closing:
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun t  ->
      let uu____5049 = univ_var_opening us in
      match uu____5049 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5089 = univ_var_opening us in
      match uu____5089 with
      | (s,us') -> let uu____5112 = subst_comp s c in (us', uu____5112)
let close_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun us  -> fun t  -> let s = univ_var_closing us in subst s t
let close_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i)))) in
      subst_comp s c
let open_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5156 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____5156
      then (lbs, t)
      else
        (let uu____5166 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____5194  ->
                  match uu____5194 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____5227 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____5227 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___190_5233 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___190_5233.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___190_5233.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___190_5233.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___190_5233.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____5166 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____5270 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____5297  ->
                                match uu____5297 with
                                | (i,us,out) ->
                                    ((i + (Prims.parse_int "1")), (u :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i, (FStar_Syntax_Syntax.U_name u)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening) in
                       match uu____5270 with
                       | (uu____5337,us,u_let_rec_opening) ->
                           let uu___191_5348 = lb in
                           let uu____5349 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___191_5348.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___191_5348.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___191_5348.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5349
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5371 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____5371
      then (lbs, t)
      else
        (let uu____5381 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____5400  ->
                  match uu____5400 with
                  | (i,out) ->
                      let uu____5419 =
                        let uu____5422 =
                          let uu____5423 =
                            let uu____5428 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____5428, i) in
                          FStar_Syntax_Syntax.NM uu____5423 in
                        uu____5422 :: out in
                      ((i + (Prims.parse_int "1")), uu____5419)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____5381 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____5459 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____5477  ->
                                match uu____5477 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____5459 with
                       | (uu____5500,u_let_rec_closing) ->
                           let uu___192_5506 = lb in
                           let uu____5507 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___192_5506.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___192_5506.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___192_5506.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___192_5506.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5507
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5518  ->
      match uu____5518 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5543  ->
                   match uu____5543 with
                   | (x,uu____5549) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5564  ->
      match uu____5564 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5586 = subst s t in (us', uu____5586)
let subst_tscheme:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun s  ->
    fun uu____5596  ->
      match uu____5596 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu____5606 = subst s1 t in (us, uu____5606)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5628  ->
              match uu____5628 with
              | (x,uu____5634) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs