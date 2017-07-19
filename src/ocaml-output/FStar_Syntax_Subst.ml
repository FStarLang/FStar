open Prims
let subst_to_string s =
  let uu____20 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____35  ->
            match uu____35 with
            | (b,uu____41) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____20 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> FStar_Pervasives_Native.None
  | s0::rest ->
      let uu____89 = f s0 in
      (match uu____89 with
       | FStar_Pervasives_Native.None  -> apply_until_some f rest
       | FStar_Pervasives_Native.Some st ->
           FStar_Pervasives_Native.Some (rest, st))
let map_some_curry f x uu___99_141 =
  match uu___99_141 with
  | FStar_Pervasives_Native.None  -> x
  | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____215 = apply_until_some f s in
  FStar_All.pipe_right uu____215 (map_some_curry g t)
let compose_subst s1 s2 =
  let s =
    FStar_List.append (FStar_Pervasives_Native.fst s1)
      (FStar_Pervasives_Native.fst s2) in
  let ropt =
    match FStar_Pervasives_Native.snd s2 with
    | FStar_Pervasives_Native.Some uu____308 ->
        FStar_Pervasives_Native.snd s2
    | uu____313 -> FStar_Pervasives_Native.snd s1 in
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
      | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed
            (FStar_Util.Inl (t', (compose_subst s' s)))
            t.FStar_Syntax_Syntax.pos
      | uu____489 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t, s))
            t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____544) ->
        let uu____569 = FStar_Unionfind.find uv in
        (match uu____569 with
         | FStar_Syntax_Syntax.Fixed t' -> force_uvar' t'
         | uu____595 -> t)
    | uu____602 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____623 = FStar_Util.physical_equality t t' in
    if uu____623
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
        let uu____730 = FStar_ST.read m in
        (match uu____730 with
         | FStar_Pervasives_Native.None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____793 = c () in force_delayed_thunk uu____793 in
                  (FStar_ST.write m (FStar_Pervasives_Native.Some t'); t')
              | uu____811 -> t)
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (FStar_Pervasives_Native.Some t'1); t'1))
    | uu____867 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____876 = FStar_Unionfind.find u' in
        (match uu____876 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____882 -> u)
    | uu____885 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___100_898  ->
           match uu___100_898 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____903 =
                 let uu____904 =
                   let uu____905 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____905 in
                 FStar_Syntax_Syntax.bv_to_name uu____904 in
               FStar_Pervasives_Native.Some uu____903
           | uu____906 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_919  ->
           match uu___101_919 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____924 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___105_925 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___105_925.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___105_925.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____924
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____940 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_953  ->
           match uu___102_953 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____958 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_971  ->
           match uu___103_971 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____976 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____998 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1004 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____1004
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1008 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____1008
let tag_with_range t s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> t
  | FStar_Pervasives_Native.Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____1055 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____1055
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____1057 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____1057
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___106_1069 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___106_1069.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___106_1069.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___107_1093 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___107_1093.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___107_1093.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___108_1095 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___108_1095.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___108_1095.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> l
  | FStar_Pervasives_Native.Some r ->
      let uu____1127 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____1127
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
      | uu____1259 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1273 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1278 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1283 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____1435,uu____1436) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1538 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1539 =
                 let uu____1544 =
                   let uu____1545 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1545 in
                 FStar_Syntax_Syntax.mk uu____1544 in
               uu____1539 FStar_Pervasives_Native.None uu____1538
           | uu____1556 ->
               let uu____1557 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____1557)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___104_1580  ->
              match uu___104_1580 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1586 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1586
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
      | uu____1622 ->
          let uu___109_1633 = t in
          let uu____1634 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1641 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1646 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1651 =
            FStar_List.map
              (fun uu____1678  ->
                 match uu____1678 with
                 | (t1,imp) ->
                     let uu____1705 = subst' s t1 in (uu____1705, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1714 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1634;
            FStar_Syntax_Syntax.effect_name = uu____1641;
            FStar_Syntax_Syntax.result_typ = uu____1646;
            FStar_Syntax_Syntax.effect_args = uu____1651;
            FStar_Syntax_Syntax.flags = uu____1714
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
      | uu____1755 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1784 = subst' s t1 in
               let uu____1785 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1784 uu____1785
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1808 = subst' s t1 in
               let uu____1809 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1808 uu____1809
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1819 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1819)
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
      | FStar_Syntax_Syntax.NT uu____1834 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1879 =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
      (FStar_List.map (shift_subst n1)) in
  (uu____1879, (FStar_Pervasives_Native.snd s))
let subst_binder' s uu____1911 =
  match uu____1911 with
  | (x,imp) ->
      let uu____1918 =
        let uu___110_1919 = x in
        let uu____1920 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___110_1919.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___110_1919.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1920
        } in
      (uu____1918, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1986 = shift_subst' i s in
               subst_binder' uu____1986 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg' s uu____2036 =
  match uu____2036 with
  | (t,imp) -> let uu____2055 = subst' s t in (uu____2055, imp)
let subst_args' s = FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____2174 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____2201 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2250  ->
                      fun uu____2251  ->
                        match (uu____2250, uu____2251) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2340 = aux n2 p2 in
                            (match uu____2340 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____2201 with
             | (pats1,n2) ->
                 ((let uu___111_2399 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___111_2399.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___111_2399.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___112_2427 = x in
              let uu____2428 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___112_2427.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___112_2427.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2428
              } in
            ((let uu___113_2437 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___113_2437.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___113_2437.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___114_2455 = x in
              let uu____2456 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___114_2455.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___114_2455.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2456
              } in
            ((let uu___115_2465 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___115_2465.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___115_2465.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_2492 = x in
              let uu____2493 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_2492.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_2492.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2493
              } in
            let t01 = subst' s1 t0 in
            ((let uu___117_2507 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___117_2507.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___117_2507.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | FStar_Pervasives_Native.None  -> lopt
  | FStar_Pervasives_Native.Some (FStar_Util.Inr uu____2550) -> lopt
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l) ->
      let uu____2560 =
        let uu____2565 =
          let uu___118_2566 = l in
          let uu____2567 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___118_2566.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____2567;
            FStar_Syntax_Syntax.cflags =
              (uu___118_2566.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____2572  ->
                 let uu____2573 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____2573)
          } in
        FStar_Util.Inl uu____2565 in
      FStar_Pervasives_Native.Some uu____2560
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
        let uu____2608 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2608 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2613 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2656 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2661 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2670 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2691 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2692 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2693 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2713 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2713 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2752 =
            let uu____2753 =
              let uu____2772 = subst' s t0 in
              let uu____2777 = subst_args' s args in (uu____2772, uu____2777) in
            FStar_Syntax_Syntax.Tm_app uu____2753 in
          mk1 uu____2752
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2914 = subst' s t1 in FStar_Util.Inl uu____2914
            | FStar_Util.Inr c ->
                let uu____2940 = subst_comp' s c in FStar_Util.Inr uu____2940 in
          let uu____2953 =
            let uu____2954 =
              let uu____2989 = subst' s t0 in
              let uu____2994 =
                let uu____3017 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____3017) in
              (uu____2989, uu____2994, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2954 in
          mk1 uu____2953
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____3143 =
            let uu____3144 =
              let uu____3173 = subst_binders' s bs in
              let uu____3180 = subst' s' body in
              let uu____3185 = push_subst_lcomp s' lopt in
              (uu____3173, uu____3180, uu____3185) in
            FStar_Syntax_Syntax.Tm_abs uu____3144 in
          mk1 uu____3143
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____3253 =
            let uu____3254 =
              let uu____3269 = subst_binders' s bs in
              let uu____3276 =
                let uu____3281 = shift_subst' n1 s in
                subst_comp' uu____3281 comp in
              (uu____3269, uu____3276) in
            FStar_Syntax_Syntax.Tm_arrow uu____3254 in
          mk1 uu____3253
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___119_3317 = x in
            let uu____3318 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_3317.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_3317.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3318
            } in
          let phi1 =
            let uu____3328 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____3328 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3489  ->
                    match uu____3489 with
                    | (pat,wopt,branch) ->
                        let uu____3557 = subst_pat' s pat in
                        (match uu____3557 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3621 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____3621 in
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
                      let uu____3725 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____3725
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___120_3741 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___120_3741.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___120_3741.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___121_3743 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___122_3744 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___122_3744.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___122_3744.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___121_3743.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___121_3743.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___123_3767 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___123_3767.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___123_3767.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3802 =
            let uu____3803 =
              let uu____3812 = subst' s t0 in
              let uu____3817 =
                let uu____3818 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____3818 in
              (uu____3812, uu____3817) in
            FStar_Syntax_Syntax.Tm_meta uu____3803 in
          mk1 uu____3802
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3898 =
            let uu____3899 =
              let uu____3908 = subst' s t0 in
              let uu____3913 =
                let uu____3914 =
                  let uu____3923 = subst' s t1 in (m, uu____3923) in
                FStar_Syntax_Syntax.Meta_monadic uu____3914 in
              (uu____3908, uu____3913) in
            FStar_Syntax_Syntax.Tm_meta uu____3899 in
          mk1 uu____3898
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3956 =
            let uu____3957 =
              let uu____3966 = subst' s t0 in
              let uu____3971 =
                let uu____3972 =
                  let uu____3983 = subst' s t1 in (m1, m2, uu____3983) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3972 in
              (uu____3966, uu____3971) in
            FStar_Syntax_Syntax.Tm_meta uu____3957 in
          mk1 uu____3956
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____4006 =
            let uu____4007 = let uu____4016 = subst' s t1 in (uu____4016, m) in
            FStar_Syntax_Syntax.Tm_meta uu____4007 in
          mk1 uu____4006
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____4129 = push_subst s t2 in compress uu____4129 in
        (FStar_Unionfind.update_in_tx memo (FStar_Pervasives_Native.Some t');
         t')
    | uu____4139 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____4145 -> compress t'
         | uu____4184 -> t')
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
             (let uu___124_4219 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___124_4219.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst bs =
  let uu____4261 =
    FStar_List.fold_right
      (fun uu____4278  ->
         fun uu____4279  ->
           match (uu____4278, uu____4279) with
           | ((x,uu____4307),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____4261 FStar_Pervasives_Native.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___125_4446 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____4447 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___125_4446.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___125_4446.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____4447
          } in
        let o1 =
          let uu____4455 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____4455 in
        let uu____4458 = aux bs' o1 in
        (match uu____4458 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    let uu____4516 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____4516
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____4549 = open_binders' bs in
      match uu____4549 with
      | (bs',opening) ->
          let uu____4586 = subst opening t in (bs', uu____4586, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____4605 = open_term' bs t in
      match uu____4605 with | (b,t1,uu____4618) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____4629 = open_binders' bs in
      match uu____4629 with
      | (bs',opening) ->
          let uu____4664 = subst_comp opening t in (bs', uu____4664)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4752 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4787 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4878  ->
                    fun uu____4879  ->
                      match (uu____4878, uu____4879) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____5049 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____5049 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____4787 with
           | (pats1,sub2,renaming1) ->
               ((let uu___126_5244 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___126_5244.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___126_5244.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___127_5269 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____5270 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_5269.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_5269.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5270
            } in
          let sub2 =
            let uu____5278 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____5278 in
          ((let uu___128_5293 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___128_5293.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___128_5293.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___129_5304 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____5305 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_5304.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_5304.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5305
            } in
          let sub2 =
            let uu____5313 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____5313 in
          ((let uu___130_5328 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___130_5328.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___130_5328.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___131_5348 = x in
            let uu____5349 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_5348.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_5348.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5349
            } in
          let t01 = subst sub1 t0 in
          ((let uu___132_5367 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___132_5367.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___132_5367.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____5372 = open_pat_aux [] [] p in
    match uu____5372 with | (p1,sub1,uu____5401) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____5434  ->
    match uu____5434 with
    | (p,wopt,e) ->
        let uu____5466 = open_pat p in
        (match uu____5466 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5491 = subst opening w in
                   FStar_Pervasives_Native.Some uu____5491 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____5501 = closing_subst bs in subst uu____5501 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____5510 = closing_subst bs in subst_comp uu____5510 c
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
            let uu___133_5561 = x in
            let uu____5562 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_5561.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_5561.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5562
            } in
          let s' =
            let uu____5570 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5570 in
          let uu____5573 = aux s' tl1 in (x1, imp) :: uu____5573 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___134_5593 = lc in
      let uu____5594 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___134_5593.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____5594;
        FStar_Syntax_Syntax.cflags =
          (uu___134_5593.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____5599  ->
             let uu____5600 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____5600)
      }
let close_pat:
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                        Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____5661 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5690 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5757  ->
                    fun uu____5758  ->
                      match (uu____5757, uu____5758) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5883 = aux sub2 p2 in
                          (match uu____5883 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____5690 with
           | (pats1,sub2) ->
               ((let uu___135_6010 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___135_6010.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___135_6010.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___136_6035 = x in
            let uu____6036 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_6035.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_6035.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____6036
            } in
          let sub2 =
            let uu____6044 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____6044 in
          ((let uu___137_6053 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___137_6053.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___137_6053.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___138_6060 = x in
            let uu____6061 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_6060.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_6060.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____6061
            } in
          let sub2 =
            let uu____6069 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____6069 in
          ((let uu___139_6078 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___139_6078.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_6078.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___140_6094 = x in
            let uu____6095 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_6094.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_6094.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____6095
            } in
          let t01 = subst sub1 t0 in
          ((let uu___141_6107 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___141_6107.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_6107.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____6114  ->
    match uu____6114 with
    | (p,wopt,e) ->
        let uu____6146 = close_pat p in
        (match uu____6146 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____6189 = subst closing w in
                   FStar_Pervasives_Native.Some uu____6189 in
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
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun t  ->
      let uu____6232 = univ_var_opening us in
      match uu____6232 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____6272 = univ_var_opening us in
      match uu____6272 with
      | (s,us') -> let uu____6295 = subst_comp s c in (us', uu____6295)
let close_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun us  ->
    fun t  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i)))) in
      subst s t
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
      let uu____6342 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____6342
      then (lbs, t)
      else
        (let uu____6352 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____6374  ->
                  match uu____6374 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____6407 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____6407 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___142_6412 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___142_6412.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___142_6412.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___142_6412.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___142_6412.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____6352 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____6442 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____6464  ->
                                match uu____6464 with
                                | (i,us,out) ->
                                    ((i + (Prims.parse_int "1")), (u :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i, (FStar_Syntax_Syntax.U_name u)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening) in
                       match uu____6442 with
                       | (uu____6504,us,u_let_rec_opening) ->
                           let uu___143_6515 = lb in
                           let uu____6516 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___143_6515.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___143_6515.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___143_6515.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____6516
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
      let uu____6540 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____6540
      then (lbs, t)
      else
        (let uu____6550 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____6564  ->
                  match uu____6564 with
                  | (i,out) ->
                      let uu____6583 =
                        let uu____6586 =
                          let uu____6587 =
                            let uu____6592 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____6592, i) in
                          FStar_Syntax_Syntax.NM uu____6587 in
                        uu____6586 :: out in
                      ((i + (Prims.parse_int "1")), uu____6583)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____6550 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____6617 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____6631  ->
                                match uu____6631 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____6617 with
                       | (uu____6654,u_let_rec_closing) ->
                           let uu___144_6660 = lb in
                           let uu____6661 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___144_6660.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___144_6660.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___144_6660.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___144_6660.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____6661
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    fun uu____6674  ->
      match uu____6674 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6695  ->
                   match uu____6695 with
                   | (x,uu____6701) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun uu____6713  ->
      match uu____6713 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____6730 = subst s t in (us', uu____6730)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6748  ->
              match uu____6748 with
              | (x,uu____6754) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))