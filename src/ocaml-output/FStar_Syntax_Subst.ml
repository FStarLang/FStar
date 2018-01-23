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
      fun uu___34_146  ->
        match uu___34_146 with
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____496 = FStar_Util.physical_equality t t' in
    if uu____496
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
        let uu____563 = FStar_ST.op_Bang m in
        (match uu____563 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____681 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____694 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____694 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____698 -> u)
    | uu____701 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___35_718  ->
           match uu___35_718 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____723 =
                 let uu____724 =
                   let uu____725 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____725 in
                 FStar_Syntax_Syntax.bv_to_name uu____724 in
               FStar_Pervasives_Native.Some uu____723
           | uu____726 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___36_743  ->
           match uu___36_743 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____748 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___40_751 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___40_751.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___40_751.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____748
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____760 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___37_776  ->
           match uu___37_776 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____781 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___38_797  ->
           match uu___38_797 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____802 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____824 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____834 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____834
      | FStar_Syntax_Syntax.U_max us ->
          let uu____838 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____838
let tag_with_range:
  'Auu____844 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____844,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____875 = FStar_Range.use_range r in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____875 in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____878 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____878
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____880 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____880
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___41_886 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___41_886.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___42_888 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___42_888.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___42_888.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___43_890 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars = (uu___43_890.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range:
  'Auu____896 .
    FStar_Ident.lident ->
      ('Auu____896,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____920 =
            let uu____921 = FStar_Range.use_range r in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____921 in
          FStar_Ident.set_lid_range l uu____920
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____935 = FStar_Range.use_range r' in
          FStar_Range.set_use_range r uu____935
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
      | uu____1038 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1048 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1053 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1058 -> tag_with_range t0 s
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
               let uu____1167 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1168 =
                 let uu____1171 =
                   let uu____1172 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1172 in
                 FStar_Syntax_Syntax.mk uu____1171 in
               uu____1168 FStar_Pervasives_Native.None uu____1167
           | uu____1182 ->
               let uu____1183 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1183)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___39_1197  ->
              match uu___39_1197 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1201 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1201
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
      | uu____1235 ->
          let uu___44_1246 = t in
          let uu____1247 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1254 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1259 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1262 =
            FStar_List.map
              (fun uu____1287  ->
                 match uu____1287 with
                 | (t1,imp) ->
                     let uu____1306 = subst' s t1 in (uu____1306, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1311 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1247;
            FStar_Syntax_Syntax.effect_name = uu____1254;
            FStar_Syntax_Syntax.result_typ = uu____1259;
            FStar_Syntax_Syntax.effect_args = uu____1262;
            FStar_Syntax_Syntax.flags = uu____1311
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
      | uu____1348 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1371 = subst' s t1 in
               let uu____1372 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1371 uu____1372
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1391 = subst' s t1 in
               let uu____1392 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1391 uu____1392
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1402 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1402)
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
      | FStar_Syntax_Syntax.NT uu____1417 -> s
let shift_subst:
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst':
  'Auu____1433 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1433)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1433)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1460 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1460, (FStar_Pervasives_Native.snd s))
let subst_binder':
  'Auu____1476 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1476) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1476) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1492  ->
      match uu____1492 with
      | (x,imp) ->
          let uu____1499 =
            let uu___45_1500 = x in
            let uu____1501 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___45_1500.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___45_1500.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1501
            } in
          (uu____1499, imp)
let subst_binders':
  'Auu____1507 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1507) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1507) FStar_Pervasives_Native.tuple2
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
                  (let uu____1567 = shift_subst' i s in
                   subst_binder' uu____1567 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg':
  'Auu____1593 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1593)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1593)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1613  ->
      match uu____1613 with
      | (t,imp) -> let uu____1626 = subst' s t in (uu____1626, imp)
let subst_args':
  'Auu____1633 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1633)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1633)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1721 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1742 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1796  ->
                      fun uu____1797  ->
                        match (uu____1796, uu____1797) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1876 = aux n2 p2 in
                            (match uu____1876 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1742 with
             | (pats1,n2) ->
                 ((let uu___46_1934 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___46_1934.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___47_1960 = x in
              let uu____1961 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___47_1960.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___47_1960.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1961
              } in
            ((let uu___48_1967 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___48_1967.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___49_1983 = x in
              let uu____1984 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___49_1983.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___49_1983.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1984
              } in
            ((let uu___50_1990 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___50_1990.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___51_2011 = x in
              let uu____2012 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___51_2011.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___51_2011.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2012
              } in
            let t01 = subst' s1 t0 in
            ((let uu___52_2021 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___52_2021.FStar_Syntax_Syntax.p)
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
          let uu____2041 =
            let uu___53_2042 = rc in
            let uu____2043 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___53_2042.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2043;
              FStar_Syntax_Syntax.residual_flags =
                (uu___53_2042.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2041
let push_subst:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2070 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2070 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2073 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2100 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2105 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2110 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2135 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2136 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2137 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2153 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2153 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2182 =
            let uu____2183 =
              let uu____2198 = subst' s t0 in
              let uu____2201 = subst_args' s args in (uu____2198, uu____2201) in
            FStar_Syntax_Syntax.Tm_app uu____2183 in
          mk1 uu____2182
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2296 = subst' s t1 in FStar_Util.Inl uu____2296
            | FStar_Util.Inr c ->
                let uu____2310 = subst_comp' s c in FStar_Util.Inr uu____2310 in
          let uu____2317 =
            let uu____2318 =
              let uu____2345 = subst' s t0 in
              let uu____2348 =
                let uu____2365 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2365) in
              (uu____2345, uu____2348, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2318 in
          mk1 uu____2317
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2449 =
            let uu____2450 =
              let uu____2467 = subst_binders' s bs in
              let uu____2474 = subst' s' body in
              let uu____2477 = push_subst_lcomp s' lopt in
              (uu____2467, uu____2474, uu____2477) in
            FStar_Syntax_Syntax.Tm_abs uu____2450 in
          mk1 uu____2449
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2513 =
            let uu____2514 =
              let uu____2527 = subst_binders' s bs in
              let uu____2534 =
                let uu____2537 = shift_subst' n1 s in
                subst_comp' uu____2537 comp in
              (uu____2527, uu____2534) in
            FStar_Syntax_Syntax.Tm_arrow uu____2514 in
          mk1 uu____2513
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___54_2569 = x in
            let uu____2570 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___54_2569.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___54_2569.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2570
            } in
          let phi1 =
            let uu____2576 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2576 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2703  ->
                    match uu____2703 with
                    | (pat,wopt,branch) ->
                        let uu____2749 = subst_pat' s pat in
                        (match uu____2749 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2797 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2797 in
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
                      let uu____2882 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2882
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___55_2897 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___55_2897.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___55_2897.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___56_2899 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___56_2899.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___56_2899.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2926 =
            let uu____2927 =
              let uu____2934 = subst' s t0 in
              let uu____2937 =
                let uu____2938 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2938 in
              (uu____2934, uu____2937) in
            FStar_Syntax_Syntax.Tm_meta uu____2927 in
          mk1 uu____2926
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2998 =
            let uu____2999 =
              let uu____3006 = subst' s t0 in
              let uu____3009 =
                let uu____3010 =
                  let uu____3017 = subst' s t1 in (m, uu____3017) in
                FStar_Syntax_Syntax.Meta_monadic uu____3010 in
              (uu____3006, uu____3009) in
            FStar_Syntax_Syntax.Tm_meta uu____2999 in
          mk1 uu____2998
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3036 =
            let uu____3037 =
              let uu____3044 = subst' s t0 in
              let uu____3047 =
                let uu____3048 =
                  let uu____3057 = subst' s t1 in (m1, m2, uu____3057) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3048 in
              (uu____3044, uu____3047) in
            FStar_Syntax_Syntax.Tm_meta uu____3037 in
          mk1 uu____3036
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3070 =
            let uu____3071 = let uu____3078 = subst' s t1 in (uu____3078, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3071 in
          mk1 uu____3070
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3141 = push_subst s t2 in compress uu____3141 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3169 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3173 -> compress t'
         | uu____3198 -> t')
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let set_use_range:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      let uu____3225 =
        let uu____3226 =
          let uu____3229 =
            let uu____3230 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu____3230 in
          FStar_Pervasives_Native.Some uu____3229 in
        ([], uu____3226) in
      subst' uu____3225 t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3264 =
      FStar_List.fold_right
        (fun uu____3287  ->
           fun uu____3288  ->
             match (uu____3287, uu____3288) with
             | ((x,uu____3316),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3264 FStar_Pervasives_Native.fst
let open_binders':
  'Auu____3349 .
    (FStar_Syntax_Syntax.bv,'Auu____3349) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3349) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___57_3455 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3456 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___57_3455.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___57_3455.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3456
            } in
          let o1 =
            let uu____3462 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3462 in
          let uu____3465 = aux bs' o1 in
          (match uu____3465 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let open_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3523 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3523
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3556 = open_binders' bs in
      match uu____3556 with
      | (bs',opening) ->
          let uu____3593 = subst opening t in (bs', uu____3593, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3612 = open_term' bs t in
      match uu____3612 with | (b,t1,uu____3625) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3636 = open_binders' bs in
      match uu____3636 with
      | (bs',opening) ->
          let uu____3671 = subst_comp opening t in (bs', uu____3671)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3751 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3780 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3872  ->
                    fun uu____3873  ->
                      match (uu____3872, uu____3873) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4021 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4021 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3780 with
           | (pats1,sub2,renaming1) ->
               ((let uu___58_4191 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___58_4191.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___59_4210 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4211 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___59_4210.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___59_4210.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4211
            } in
          let sub2 =
            let uu____4217 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4217 in
          ((let uu___60_4231 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___60_4231.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___61_4240 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4241 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___61_4240.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___61_4240.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4241
            } in
          let sub2 =
            let uu____4247 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4247 in
          ((let uu___62_4261 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___62_4261.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___63_4275 = x in
            let uu____4276 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___63_4275.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___63_4275.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4276
            } in
          let t01 = subst sub1 t0 in
          ((let uu___64_4291 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___64_4291.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4294 = open_pat_aux [] [] p in
    match uu____4294 with | (p1,sub1,uu____4321) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4348  ->
    match uu____4348 with
    | (p,wopt,e) ->
        let uu____4368 = open_pat p in
        (match uu____4368 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4387 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4387 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4397 = closing_subst bs in subst uu____4397 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4406 = closing_subst bs in subst_comp uu____4406 c
let close_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___65_4457 = x in
            let uu____4458 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___65_4457.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___65_4457.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4458
            } in
          let s' =
            let uu____4464 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4464 in
          let uu____4467 = aux s' tl1 in (x1, imp) :: uu____4467 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4489  ->
           let uu____4490 = FStar_Syntax_Syntax.lcomp_comp lc in
           subst_comp s uu____4490)
let close_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4537 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4560 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4626  ->
                    fun uu____4627  ->
                      match (uu____4626, uu____4627) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4730 = aux sub2 p2 in
                          (match uu____4730 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4560 with
           | (pats1,sub2) ->
               ((let uu___66_4832 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___66_4832.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___67_4851 = x in
            let uu____4852 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___67_4851.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___67_4851.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4852
            } in
          let sub2 =
            let uu____4858 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4858 in
          ((let uu___68_4866 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___68_4866.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___69_4871 = x in
            let uu____4872 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___69_4871.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___69_4871.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4872
            } in
          let sub2 =
            let uu____4878 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4878 in
          ((let uu___70_4886 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___70_4886.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___71_4896 = x in
            let uu____4897 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___71_4896.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___71_4896.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4897
            } in
          let t01 = subst sub1 t0 in
          ((let uu___72_4906 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___72_4906.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4911  ->
    match uu____4911 with
    | (p,wopt,e) ->
        let uu____4931 = close_pat p in
        (match uu____4931 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4962 = subst closing w in
                   FStar_Pervasives_Native.Some uu____4962 in
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
      let uu____5017 = univ_var_opening us in
      match uu____5017 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5057 = univ_var_opening us in
      match uu____5057 with
      | (s,us') -> let uu____5080 = subst_comp s c in (us', uu____5080)
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
      let uu____5124 =
        let uu____5135 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5135
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5168  ->
                 match uu____5168 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5201 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5201 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___73_5207 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___73_5207.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___73_5207.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___73_5207.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___73_5207.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____5124 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5245 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5273  ->
                             match uu____5273 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5245 with
                    | (uu____5314,us,u_let_rec_opening) ->
                        let uu___74_5325 = lb in
                        let uu____5326 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5329 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___74_5325.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5326;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___74_5325.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5329
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
      let uu____5351 =
        let uu____5358 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5358
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5380  ->
                 match uu____5380 with
                 | (i,out) ->
                     let uu____5399 =
                       let uu____5402 =
                         let uu____5403 =
                           let uu____5408 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5408, i) in
                         FStar_Syntax_Syntax.NM uu____5403 in
                       uu____5402 :: out in
                     ((i + (Prims.parse_int "1")), uu____5399)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____5351 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5440 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5458  ->
                             match uu____5458 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5440 with
                    | (uu____5481,u_let_rec_closing) ->
                        let uu___75_5487 = lb in
                        let uu____5488 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5491 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___75_5487.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___75_5487.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5488;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___75_5487.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5491
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5502  ->
      match uu____5502 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5527  ->
                   match uu____5527 with
                   | (x,uu____5533) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5548  ->
      match uu____5548 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5570 = subst s t in (us', uu____5570)
let subst_tscheme:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun s  ->
    fun uu____5580  ->
      match uu____5580 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu____5590 = subst s1 t in (us, uu____5590)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5612  ->
              match uu____5612 with
              | (x,uu____5618) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs