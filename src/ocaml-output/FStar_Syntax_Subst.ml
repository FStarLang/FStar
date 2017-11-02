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
  'Auu____53 'Auu____54 .
    ('Auu____54 -> 'Auu____53 FStar_Pervasives_Native.option) ->
      'Auu____54 Prims.list ->
        ('Auu____54 Prims.list,'Auu____53) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____94 = f s0 in
          (match uu____94 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry:
  'Auu____120 'Auu____121 'Auu____122 .
    ('Auu____122 -> 'Auu____121 -> 'Auu____120) ->
      'Auu____120 ->
        ('Auu____122,'Auu____121) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____120
  =
  fun f  ->
    fun x  ->
      fun uu___150_146  ->
        match uu___150_146 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map:
  'Auu____174 'Auu____175 'Auu____176 .
    ('Auu____176 -> 'Auu____175 FStar_Pervasives_Native.option) ->
      'Auu____176 Prims.list ->
        ('Auu____176 Prims.list -> 'Auu____175 -> 'Auu____174) ->
          'Auu____174 -> 'Auu____174
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____220 = apply_until_some f s in
          FStar_All.pipe_right uu____220 (map_some_curry g t)
let compose_subst:
  'Auu____243 'Auu____244 .
    ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____313 ->
            FStar_Pervasives_Native.snd s2
        | uu____318 -> FStar_Pervasives_Native.snd s1 in
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
      | uu____424 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____449) ->
        let uu____474 = FStar_Syntax_Unionfind.find uv in
        (match uu____474 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____480 -> t)
    | uu____483 -> t
let force_uvar:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____500 = FStar_Util.physical_equality t t' in
    if uu____500
    then (t, false)
    else
      (let uu____512 =
         delay t'
           ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))) in
       (uu____512, true))
let rec force_delayed_thunk:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____574 = FStar_ST.op_Bang m in
        (match uu____574 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____730 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____743 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____743 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____747 -> u)
    | uu____750 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___151_767  ->
           match uu___151_767 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____772 =
                 let uu____773 =
                   let uu____774 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____774 in
                 FStar_Syntax_Syntax.bv_to_name uu____773 in
               FStar_Pervasives_Native.Some uu____772
           | uu____775 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___152_792  ->
           match uu___152_792 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____797 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___156_800 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___156_800.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___156_800.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____797
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____809 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___153_825  ->
           match uu___153_825 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____830 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___154_846  ->
           match uu___154_846 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____851 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____873 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____883 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____883
      | FStar_Syntax_Syntax.U_max us ->
          let uu____887 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____887
let tag_with_range:
  'Auu____893 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____893,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____924 = FStar_Range.use_range r in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____924 in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____927 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____927
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____929 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____929
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___157_935 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___157_935.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___158_937 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___158_937.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___158_937.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___159_939 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___159_939.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range:
  'Auu____945 .
    FStar_Ident.lident ->
      ('Auu____945,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____969 =
            let uu____970 = FStar_Range.use_range r in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____970 in
          FStar_Ident.set_lid_range l uu____969
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____984 = FStar_Range.use_range r' in
          FStar_Range.set_use_range r uu____984
let is_univ_subst: FStar_Syntax_Syntax.subst_ts -> Prims.bool =
  fun s  ->
    FStar_List.for_all
      (fun l  ->
         FStar_List.for_all
           (fun s1  ->
              match s1 with
              | FStar_Syntax_Syntax.UN uu____997 -> true
              | FStar_Syntax_Syntax.UD uu____1002 -> true
              | uu____1007 -> false) l) (FStar_Pervasives_Native.fst s)
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
      | uu____1116 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1126 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1131 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1136 ->
               let uu____1153 =
                 let uu____1154 = is_univ_subst s in
                 Prims.op_Negation uu____1154 in
               if uu____1153
               then tag_with_range t0 s
               else
                 (let uu____1162 = force_uvar t in
                  match uu____1162 with
                  | (t1,b) -> if b then subst' s t1 else tag_with_range t0 s)
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
               let uu____1272 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1273 =
                 let uu____1276 =
                   let uu____1277 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1277 in
                 FStar_Syntax_Syntax.mk uu____1276 in
               uu____1273 FStar_Pervasives_Native.None uu____1272
           | uu____1287 ->
               let uu____1288 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1288)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___155_1302  ->
              match uu___155_1302 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1306 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1306
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
      | uu____1340 ->
          let uu___160_1351 = t in
          let uu____1352 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1359 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1364 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1367 =
            FStar_List.map
              (fun uu____1392  ->
                 match uu____1392 with
                 | (t1,imp) ->
                     let uu____1411 = subst' s t1 in (uu____1411, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1416 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1352;
            FStar_Syntax_Syntax.effect_name = uu____1359;
            FStar_Syntax_Syntax.result_typ = uu____1364;
            FStar_Syntax_Syntax.effect_args = uu____1367;
            FStar_Syntax_Syntax.flags = uu____1416
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
      | uu____1453 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1476 = subst' s t1 in
               let uu____1477 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1476 uu____1477
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1496 = subst' s t1 in
               let uu____1497 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1496 uu____1497
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1507 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1507)
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
      | FStar_Syntax_Syntax.NT uu____1522 -> s
let shift_subst:
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst':
  'Auu____1538 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1538)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1538)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1565 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1565, (FStar_Pervasives_Native.snd s))
let subst_binder':
  'Auu____1581 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1581) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1581) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1597  ->
      match uu____1597 with
      | (x,imp) ->
          let uu____1604 =
            let uu___161_1605 = x in
            let uu____1606 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___161_1605.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___161_1605.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1606
            } in
          (uu____1604, imp)
let subst_binders':
  'Auu____1612 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1612) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1612) FStar_Pervasives_Native.tuple2
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
                  (let uu____1672 = shift_subst' i s in
                   subst_binder' uu____1672 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg':
  'Auu____1698 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1698)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1698)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1718  ->
      match uu____1718 with
      | (t,imp) -> let uu____1731 = subst' s t in (uu____1731, imp)
let subst_args':
  'Auu____1738 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1738)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1738)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1826 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1847 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1901  ->
                      fun uu____1902  ->
                        match (uu____1901, uu____1902) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1981 = aux n2 p2 in
                            (match uu____1981 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1847 with
             | (pats1,n2) ->
                 ((let uu___162_2039 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___162_2039.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___163_2065 = x in
              let uu____2066 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___163_2065.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___163_2065.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2066
              } in
            ((let uu___164_2072 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___164_2072.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___165_2088 = x in
              let uu____2089 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___165_2088.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___165_2088.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2089
              } in
            ((let uu___166_2095 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___166_2095.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___167_2116 = x in
              let uu____2117 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___167_2116.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___167_2116.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2117
              } in
            let t01 = subst' s1 t0 in
            ((let uu___168_2126 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___168_2126.FStar_Syntax_Syntax.p)
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
          let uu____2146 =
            let uu___169_2147 = rc in
            let uu____2148 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___169_2147.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2148;
              FStar_Syntax_Syntax.residual_flags =
                (uu___169_2147.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2146
let push_subst:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2175 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2175 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2178 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2205 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2210 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2219 -> subst' s t
      | FStar_Syntax_Syntax.Tm_type uu____2236 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2237 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2238 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2254 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2254 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2283 =
            let uu____2284 =
              let uu____2299 = subst' s t0 in
              let uu____2302 = subst_args' s args in (uu____2299, uu____2302) in
            FStar_Syntax_Syntax.Tm_app uu____2284 in
          mk1 uu____2283
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2397 = subst' s t1 in FStar_Util.Inl uu____2397
            | FStar_Util.Inr c ->
                let uu____2411 = subst_comp' s c in FStar_Util.Inr uu____2411 in
          let uu____2418 =
            let uu____2419 =
              let uu____2446 = subst' s t0 in
              let uu____2449 =
                let uu____2466 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2466) in
              (uu____2446, uu____2449, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2419 in
          mk1 uu____2418
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2550 =
            let uu____2551 =
              let uu____2568 = subst_binders' s bs in
              let uu____2575 = subst' s' body in
              let uu____2578 = push_subst_lcomp s' lopt in
              (uu____2568, uu____2575, uu____2578) in
            FStar_Syntax_Syntax.Tm_abs uu____2551 in
          mk1 uu____2550
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2614 =
            let uu____2615 =
              let uu____2628 = subst_binders' s bs in
              let uu____2635 =
                let uu____2638 = shift_subst' n1 s in
                subst_comp' uu____2638 comp in
              (uu____2628, uu____2635) in
            FStar_Syntax_Syntax.Tm_arrow uu____2615 in
          mk1 uu____2614
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___170_2670 = x in
            let uu____2671 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___170_2670.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___170_2670.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2671
            } in
          let phi1 =
            let uu____2677 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2677 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2804  ->
                    match uu____2804 with
                    | (pat,wopt,branch) ->
                        let uu____2850 = subst_pat' s pat in
                        (match uu____2850 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2898 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2898 in
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
                      let uu____2983 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2983
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___171_2998 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___171_2998.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___171_2998.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___172_3000 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___172_3000.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___172_3000.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3027 =
            let uu____3028 =
              let uu____3035 = subst' s t0 in
              let uu____3038 =
                let uu____3039 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____3039 in
              (uu____3035, uu____3038) in
            FStar_Syntax_Syntax.Tm_meta uu____3028 in
          mk1 uu____3027
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3099 =
            let uu____3100 =
              let uu____3107 = subst' s t0 in
              let uu____3110 =
                let uu____3111 =
                  let uu____3118 = subst' s t1 in (m, uu____3118) in
                FStar_Syntax_Syntax.Meta_monadic uu____3111 in
              (uu____3107, uu____3110) in
            FStar_Syntax_Syntax.Tm_meta uu____3100 in
          mk1 uu____3099
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3137 =
            let uu____3138 =
              let uu____3145 = subst' s t0 in
              let uu____3148 =
                let uu____3149 =
                  let uu____3158 = subst' s t1 in (m1, m2, uu____3158) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3149 in
              (uu____3145, uu____3148) in
            FStar_Syntax_Syntax.Tm_meta uu____3138 in
          mk1 uu____3137
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3171 =
            let uu____3172 = let uu____3179 = subst' s t1 in (uu____3179, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3172 in
          mk1 uu____3171
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3242 = push_subst s t2 in compress uu____3242 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3262 ->
        let uu____3263 = force_uvar t1 in
        (match uu____3263 with
         | (t',uu____3271) ->
             (match t'.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3276 -> compress t'
              | uu____3301 -> t'))
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let set_use_range:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      let uu____3328 =
        let uu____3329 =
          let uu____3332 =
            let uu____3333 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu____3333 in
          FStar_Pervasives_Native.Some uu____3332 in
        ([], uu____3329) in
      subst' uu____3328 t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3367 =
      FStar_List.fold_right
        (fun uu____3390  ->
           fun uu____3391  ->
             match (uu____3390, uu____3391) with
             | ((x,uu____3419),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3367 FStar_Pervasives_Native.fst
let open_binders':
  'Auu____3452 .
    (FStar_Syntax_Syntax.bv,'Auu____3452) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3452) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___173_3558 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3559 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___173_3558.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___173_3558.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3559
            } in
          let o1 =
            let uu____3565 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3565 in
          let uu____3568 = aux bs' o1 in
          (match uu____3568 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let open_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3626 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3626
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3659 = open_binders' bs in
      match uu____3659 with
      | (bs',opening) ->
          let uu____3696 = subst opening t in (bs', uu____3696, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3715 = open_term' bs t in
      match uu____3715 with | (b,t1,uu____3728) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3739 = open_binders' bs in
      match uu____3739 with
      | (bs',opening) ->
          let uu____3774 = subst_comp opening t in (bs', uu____3774)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3854 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3883 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3975  ->
                    fun uu____3976  ->
                      match (uu____3975, uu____3976) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4124 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4124 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3883 with
           | (pats1,sub2,renaming1) ->
               ((let uu___174_4294 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___174_4294.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___175_4313 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4314 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___175_4313.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___175_4313.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4314
            } in
          let sub2 =
            let uu____4320 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4320 in
          ((let uu___176_4334 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___176_4334.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___177_4343 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4344 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___177_4343.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___177_4343.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4344
            } in
          let sub2 =
            let uu____4350 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4350 in
          ((let uu___178_4364 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___178_4364.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___179_4378 = x in
            let uu____4379 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___179_4378.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___179_4378.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4379
            } in
          let t01 = subst sub1 t0 in
          ((let uu___180_4394 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___180_4394.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4397 = open_pat_aux [] [] p in
    match uu____4397 with | (p1,sub1,uu____4424) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4451  ->
    match uu____4451 with
    | (p,wopt,e) ->
        let uu____4471 = open_pat p in
        (match uu____4471 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4490 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4490 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4500 = closing_subst bs in subst uu____4500 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4509 = closing_subst bs in subst_comp uu____4509 c
let close_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___181_4560 = x in
            let uu____4561 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___181_4560.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___181_4560.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4561
            } in
          let s' =
            let uu____4567 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4567 in
          let uu____4570 = aux s' tl1 in (x1, imp) :: uu____4570 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___182_4590 = lc in
      let uu____4591 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___182_4590.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4591;
        FStar_Syntax_Syntax.cflags =
          (uu___182_4590.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4596  ->
             let uu____4597 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____4597)
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
      | FStar_Syntax_Syntax.Pat_constant uu____4644 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4667 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4733  ->
                    fun uu____4734  ->
                      match (uu____4733, uu____4734) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4837 = aux sub2 p2 in
                          (match uu____4837 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4667 with
           | (pats1,sub2) ->
               ((let uu___183_4939 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___183_4939.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___184_4958 = x in
            let uu____4959 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___184_4958.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___184_4958.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4959
            } in
          let sub2 =
            let uu____4965 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4965 in
          ((let uu___185_4973 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___185_4973.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___186_4978 = x in
            let uu____4979 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___186_4978.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___186_4978.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4979
            } in
          let sub2 =
            let uu____4985 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4985 in
          ((let uu___187_4993 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___187_4993.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___188_5003 = x in
            let uu____5004 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___188_5003.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___188_5003.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5004
            } in
          let t01 = subst sub1 t0 in
          ((let uu___189_5013 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___189_5013.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____5018  ->
    match uu____5018 with
    | (p,wopt,e) ->
        let uu____5038 = close_pat p in
        (match uu____5038 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5069 = subst closing w in
                   FStar_Pervasives_Native.Some uu____5069 in
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
      let uu____5124 = univ_var_opening us in
      match uu____5124 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5164 = univ_var_opening us in
      match uu____5164 with
      | (s,us') -> let uu____5187 = subst_comp s c in (us', uu____5187)
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
      let uu____5231 =
        let uu____5242 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5242
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5275  ->
                 match uu____5275 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5308 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5308 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___190_5314 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___190_5314.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___190_5314.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___190_5314.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___190_5314.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____5231 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5352 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5380  ->
                             match uu____5380 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5352 with
                    | (uu____5421,us,u_let_rec_opening) ->
                        let uu___191_5432 = lb in
                        let uu____5433 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5436 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___191_5432.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5433;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___191_5432.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5436
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5458 =
        let uu____5465 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5465
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5487  ->
                 match uu____5487 with
                 | (i,out) ->
                     let uu____5506 =
                       let uu____5509 =
                         let uu____5510 =
                           let uu____5515 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5515, i) in
                         FStar_Syntax_Syntax.NM uu____5510 in
                       uu____5509 :: out in
                     ((i + (Prims.parse_int "1")), uu____5506)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____5458 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5547 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5565  ->
                             match uu____5565 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5547 with
                    | (uu____5588,u_let_rec_closing) ->
                        let uu___192_5594 = lb in
                        let uu____5595 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5598 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___192_5594.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___192_5594.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5595;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___192_5594.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5598
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5609  ->
      match uu____5609 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5634  ->
                   match uu____5634 with
                   | (x,uu____5640) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5655  ->
      match uu____5655 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5677 = subst s t in (us', uu____5677)
let subst_tscheme:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun s  ->
    fun uu____5687  ->
      match uu____5687 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu____5697 = subst s1 t in (us, uu____5697)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5719  ->
              match uu____5719 with
              | (x,uu____5725) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs