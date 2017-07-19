open Prims
let subst_to_string s =
  let uu____22 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____40  ->
            match uu____40 with
            | (b,uu____46) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____22 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> FStar_Pervasives_Native.None
  | s0::rest ->
      let uu____98 = f s0 in
      (match uu____98 with
       | FStar_Pervasives_Native.None  -> apply_until_some f rest
       | FStar_Pervasives_Native.Some st ->
           FStar_Pervasives_Native.Some (rest, st))
let map_some_curry f x uu___103_156 =
  match uu___103_156 with
  | FStar_Pervasives_Native.None  -> x
  | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____237 = apply_until_some f s in
  FStar_All.pipe_right uu____237 (map_some_curry g t)
let compose_subst s1 s2 =
  let s =
    FStar_List.append (FStar_Pervasives_Native.fst s1)
      (FStar_Pervasives_Native.fst s2) in
  let ropt =
    match FStar_Pervasives_Native.snd s2 with
    | FStar_Pervasives_Native.Some uu____334 ->
        FStar_Pervasives_Native.snd s2
    | uu____339 -> FStar_Pervasives_Native.snd s1 in
  (s, ropt)
let delay:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
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
      | uu____463 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____499) ->
        let uu____532 = FStar_Syntax_Unionfind.find uv in
        (match uu____532 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____540 -> t)
    | uu____543 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____565 = FStar_Util.physical_equality t t' in
    if uu____565
    then t
    else
      delay t'
        ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
let rec force_delayed_thunk:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____653 = FStar_ST.read m in
        (match uu____653 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (FStar_Pervasives_Native.Some t'1); t'1))
    | uu____703 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____717 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____717 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____721 -> u)
    | uu____724 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_743  ->
           match uu___104_743 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____748 =
                 let uu____749 =
                   let uu____750 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____750 in
                 FStar_Syntax_Syntax.bv_to_name uu____749 in
               FStar_Pervasives_Native.Some uu____748
           | uu____751 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_770  ->
           match uu___105_770 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____775 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_778 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_778.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_778.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____775
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____793 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_811  ->
           match uu___106_811 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____816 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___107_834  ->
           match uu___107_834 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____839 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____863 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____873 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____873
      | FStar_Syntax_Syntax.U_max us ->
          let uu____877 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____877
let tag_with_range t s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> t
  | FStar_Pervasives_Native.Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____928 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____928
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____930 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____930
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___110_936 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.p = (uu___110_936.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___111_938 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___111_938.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___111_938.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___112_940 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___112_940.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___112_940.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> l
  | FStar_Pervasives_Native.Some r ->
      let uu____975 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____975
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' -> FStar_Range.set_use_range r r'
let rec subst':
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1109 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1123 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1128 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1133 -> tag_with_range t0 s
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
               let uu____1262 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1263 =
                 let uu____1268 =
                   let uu____1269 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1269 in
                 FStar_Syntax_Syntax.mk uu____1268 in
               uu____1263 FStar_Pervasives_Native.None uu____1262
           | uu____1280 ->
               let uu____1281 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1281)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___108_1297  ->
              match uu___108_1297 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1303 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1303
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
      | uu____1339 ->
          let uu___113_1350 = t in
          let uu____1351 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1358 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1363 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1368 =
            FStar_List.map
              (fun uu____1399  ->
                 match uu____1399 with
                 | (t1,imp) ->
                     let uu____1426 = subst' s t1 in (uu____1426, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1435 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1351;
            FStar_Syntax_Syntax.effect_name = uu____1358;
            FStar_Syntax_Syntax.result_typ = uu____1363;
            FStar_Syntax_Syntax.effect_args = uu____1368;
            FStar_Syntax_Syntax.flags = uu____1435
          }
and subst_comp':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1476 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1505 = subst' s t1 in
               let uu____1506 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1505 uu____1506
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1529 = subst' s t1 in
               let uu____1530 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1529 uu____1530
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1540 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1540)
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
      | FStar_Syntax_Syntax.NT uu____1557 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1607 =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
      (FStar_List.map (shift_subst n1)) in
  (uu____1607, (FStar_Pervasives_Native.snd s))
let subst_binder' s uu____1642 =
  match uu____1642 with
  | (x,imp) ->
      let uu____1649 =
        let uu___114_1650 = x in
        let uu____1651 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___114_1650.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___114_1650.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1651
        } in
      (uu____1649, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1722 = shift_subst' i s in
               subst_binder' uu____1722 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg' s uu____1777 =
  match uu____1777 with
  | (t,imp) -> let uu____1796 = subst' s t in (uu____1796, imp)
let subst_args' s = FStar_List.map (subst_arg' s)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1908 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1929 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1983  ->
                      fun uu____1984  ->
                        match (uu____1983, uu____1984) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2063 = aux n2 p2 in
                            (match uu____2063 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1929 with
             | (pats1,n2) ->
                 ((let uu___115_2121 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___115_2121.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_2147 = x in
              let uu____2148 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_2147.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_2147.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2148
              } in
            ((let uu___117_2156 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___117_2156.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___118_2172 = x in
              let uu____2173 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___118_2172.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___118_2172.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2173
              } in
            ((let uu___119_2181 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___119_2181.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___120_2206 = x in
              let uu____2207 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_2206.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_2206.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2207
              } in
            let t01 = subst' s1 t0 in
            ((let uu___121_2220 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___121_2220.FStar_Syntax_Syntax.p)
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
          let uu____2244 =
            let uu___122_2245 = rc in
            let uu____2246 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___122_2245.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2246;
              FStar_Syntax_Syntax.residual_flags =
                (uu___122_2245.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2244
let push_subst:
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2289 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2289 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2294 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2327 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2332 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2341 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2366 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2367 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2368 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2388 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2388 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2427 =
            let uu____2428 =
              let uu____2447 = subst' s t0 in
              let uu____2452 = subst_args' s args in (uu____2447, uu____2452) in
            FStar_Syntax_Syntax.Tm_app uu____2428 in
          mk1 uu____2427
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2589 = subst' s t1 in FStar_Util.Inl uu____2589
            | FStar_Util.Inr c ->
                let uu____2615 = subst_comp' s c in FStar_Util.Inr uu____2615 in
          let uu____2628 =
            let uu____2629 =
              let uu____2664 = subst' s t0 in
              let uu____2669 =
                let uu____2692 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2692) in
              (uu____2664, uu____2669, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2629 in
          mk1 uu____2628
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2800 =
            let uu____2801 =
              let uu____2820 = subst_binders' s bs in
              let uu____2827 = subst' s' body in
              let uu____2832 = push_subst_lcomp s' lopt in
              (uu____2820, uu____2827, uu____2832) in
            FStar_Syntax_Syntax.Tm_abs uu____2801 in
          mk1 uu____2800
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2874 =
            let uu____2875 =
              let uu____2890 = subst_binders' s bs in
              let uu____2897 =
                let uu____2902 = shift_subst' n1 s in
                subst_comp' uu____2902 comp in
              (uu____2890, uu____2897) in
            FStar_Syntax_Syntax.Tm_arrow uu____2875 in
          mk1 uu____2874
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___123_2940 = x in
            let uu____2941 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_2940.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_2940.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2941
            } in
          let phi1 =
            let uu____2951 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2951 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3114  ->
                    match uu____3114 with
                    | (pat,wopt,branch) ->
                        let uu____3176 = subst_pat' s pat in
                        (match uu____3176 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3240 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____3240 in
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
                      let uu____3351 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____3351
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___124_3368 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_3368.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_3368.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___125_3370 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_3370.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_3370.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3405 =
            let uu____3406 =
              let uu____3415 = subst' s t0 in
              let uu____3420 =
                let uu____3421 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____3421 in
              (uu____3415, uu____3420) in
            FStar_Syntax_Syntax.Tm_meta uu____3406 in
          mk1 uu____3405
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3501 =
            let uu____3502 =
              let uu____3511 = subst' s t0 in
              let uu____3516 =
                let uu____3517 =
                  let uu____3526 = subst' s t1 in (m, uu____3526) in
                FStar_Syntax_Syntax.Meta_monadic uu____3517 in
              (uu____3511, uu____3516) in
            FStar_Syntax_Syntax.Tm_meta uu____3502 in
          mk1 uu____3501
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3559 =
            let uu____3560 =
              let uu____3569 = subst' s t0 in
              let uu____3574 =
                let uu____3575 =
                  let uu____3586 = subst' s t1 in (m1, m2, uu____3586) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3575 in
              (uu____3569, uu____3574) in
            FStar_Syntax_Syntax.Tm_meta uu____3560 in
          mk1 uu____3559
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3609 =
            let uu____3610 = let uu____3619 = subst' s t1 in (uu____3619, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3610 in
          mk1 uu____3609
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3699 = push_subst s t2 in compress uu____3699 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3709 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3715 -> compress t'
         | uu____3744 -> t')
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let set_use_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun t  ->
      subst'
        ([],
          (FStar_Pervasives_Native.Some
             (let uu___126_3784 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___126_3784.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3813 =
      FStar_List.fold_right
        (fun uu____3836  ->
           fun uu____3837  ->
             match (uu____3836, uu____3837) with
             | ((x,uu____3865),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3813 FStar_Pervasives_Native.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___127_4006 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____4007 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___127_4006.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___127_4006.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____4007
          } in
        let o1 =
          let uu____4015 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____4015 in
        let uu____4018 = aux bs' o1 in
        (match uu____4018 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    let uu____4077 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____4077
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____4112 = open_binders' bs in
      match uu____4112 with
      | (bs',opening) ->
          let uu____4149 = subst opening t in (bs', uu____4149, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____4170 = open_term' bs t in
      match uu____4170 with | (b,t1,uu____4183) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____4196 = open_binders' bs in
      match uu____4196 with
      | (bs',opening) ->
          let uu____4231 = subst_comp opening t in (bs', uu____4231)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4312 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4341 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4433  ->
                    fun uu____4434  ->
                      match (uu____4433, uu____4434) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4582 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4582 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____4341 with
           | (pats1,sub2,renaming1) ->
               ((let uu___128_4752 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_4752.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___129_4771 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4772 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_4771.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_4771.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4772
            } in
          let sub2 =
            let uu____4780 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4780 in
          ((let uu___130_4794 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___130_4794.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___131_4803 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4804 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_4803.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_4803.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4804
            } in
          let sub2 =
            let uu____4812 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4812 in
          ((let uu___132_4826 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___132_4826.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_4844 = x in
            let uu____4845 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_4844.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_4844.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4845
            } in
          let t01 = subst sub1 t0 in
          ((let uu___134_4862 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_4862.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4865 = open_pat_aux [] [] p in
    match uu____4865 with | (p1,sub1,uu____4892) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4920  ->
    match uu____4920 with
    | (p,wopt,e) ->
        let uu____4948 = open_pat p in
        (match uu____4948 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4973 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4973 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4985 = closing_subst bs in subst uu____4985 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4996 = closing_subst bs in subst_comp uu____4996 c
let close_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___135_5048 = x in
            let uu____5049 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_5048.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_5048.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5049
            } in
          let s' =
            let uu____5057 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5057 in
          let uu____5060 = aux s' tl1 in (x1, imp) :: uu____5060 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___136_5082 = lc in
      let uu____5083 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___136_5082.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____5083;
        FStar_Syntax_Syntax.cflags =
          (uu___136_5082.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____5090  ->
             let uu____5091 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____5091)
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
      | FStar_Syntax_Syntax.Pat_constant uu____5139 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5162 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5228  ->
                    fun uu____5229  ->
                      match (uu____5228, uu____5229) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5332 = aux sub2 p2 in
                          (match uu____5332 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____5162 with
           | (pats1,sub2) ->
               ((let uu___137_5434 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___137_5434.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___138_5453 = x in
            let uu____5454 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_5453.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_5453.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5454
            } in
          let sub2 =
            let uu____5462 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5462 in
          ((let uu___139_5470 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___139_5470.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___140_5475 = x in
            let uu____5476 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_5475.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_5475.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5476
            } in
          let sub2 =
            let uu____5484 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5484 in
          ((let uu___141_5492 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___141_5492.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_5506 = x in
            let uu____5507 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_5506.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_5506.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5507
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_5518 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___143_5518.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____5524  ->
    match uu____5524 with
    | (p,wopt,e) ->
        let uu____5552 = close_pat p in
        (match uu____5552 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5589 = subst closing w in
                   FStar_Pervasives_Native.Some uu____5589 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_names)
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
      let uu____5648 = univ_var_opening us in
      match uu____5648 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5690 = univ_var_opening us in
      match uu____5690 with
      | (s,us') -> let uu____5713 = subst_comp s c in (us', uu____5713)
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
      let uu____5763 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____5763
      then (lbs, t)
      else
        (let uu____5773 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____5801  ->
                  match uu____5801 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____5834 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____5834 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___144_5840 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___144_5840.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___144_5840.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___144_5840.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___144_5840.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____5773 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____5877 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____5904  ->
                                match uu____5904 with
                                | (i,us,out) ->
                                    ((i + (Prims.parse_int "1")), (u :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i, (FStar_Syntax_Syntax.U_name u)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening) in
                       match uu____5877 with
                       | (uu____5944,us,u_let_rec_opening) ->
                           let uu___145_5955 = lb in
                           let uu____5956 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___145_5955.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___145_5955.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___145_5955.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5956
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
      let uu____5982 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____5982
      then (lbs, t)
      else
        (let uu____5992 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____6011  ->
                  match uu____6011 with
                  | (i,out) ->
                      let uu____6030 =
                        let uu____6033 =
                          let uu____6034 =
                            let uu____6039 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____6039, i) in
                          FStar_Syntax_Syntax.NM uu____6034 in
                        uu____6033 :: out in
                      ((i + (Prims.parse_int "1")), uu____6030)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____5992 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____6070 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____6088  ->
                                match uu____6088 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____6070 with
                       | (uu____6111,u_let_rec_closing) ->
                           let uu___146_6117 = lb in
                           let uu____6118 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___146_6117.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___146_6117.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___146_6117.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___146_6117.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____6118
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    fun uu____6133  ->
      match uu____6133 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6158  ->
                   match uu____6158 with
                   | (x,uu____6164) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun uu____6181  ->
      match uu____6181 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____6203 = subst s t in (us', uu____6203)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6226  ->
              match uu____6226 with
              | (x,uu____6232) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  -> closing_subst bs