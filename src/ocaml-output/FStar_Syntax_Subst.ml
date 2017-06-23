open Prims
let subst_to_string s =
  let uu____16 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____27  ->
            match uu____27 with
            | (b,uu____31) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____16 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> FStar_Pervasives_Native.None
  | s0::rest ->
      let uu____70 = f s0 in
      (match uu____70 with
       | FStar_Pervasives_Native.None  -> apply_until_some f rest
       | FStar_Pervasives_Native.Some st ->
           FStar_Pervasives_Native.Some (rest, st))
let map_some_curry f x uu___103_116 =
  match uu___103_116 with
  | FStar_Pervasives_Native.None  -> x
  | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____184 = apply_until_some f s in
  FStar_All.pipe_right uu____184 (map_some_curry g t)
let compose_subst s1 s2 =
  let s =
    FStar_List.append (FStar_Pervasives_Native.fst s1)
      (FStar_Pervasives_Native.fst s2) in
  let ropt =
    match FStar_Pervasives_Native.snd s2 with
    | FStar_Pervasives_Native.Some uu____243 ->
        FStar_Pervasives_Native.snd s2
    | uu____246 -> FStar_Pervasives_Native.snd s1 in
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
      | uu____314 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____335) ->
        let uu____352 = FStar_Syntax_Unionfind.find uv in
        (match uu____352 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____357 -> t)
    | uu____359 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____373 = FStar_Util.physical_equality t t' in
    if uu____373
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
        let uu____421 = FStar_ST.read m in
        (match uu____421 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (FStar_Pervasives_Native.Some t'1); t'1))
    | uu____450 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____460 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____460 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____463 -> u)
    | uu____465 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_481  ->
           match uu___104_481 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____485 =
                 let uu____486 =
                   let uu____487 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____487 in
                 FStar_Syntax_Syntax.bv_to_name uu____486 in
               FStar_Pervasives_Native.Some uu____485
           | uu____488 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_504  ->
           match uu___105_504 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____508 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_511 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_511.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_511.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____508
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____520 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_535  ->
           match uu___106_535 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____539 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___107_554  ->
           match uu___107_554 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____558 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____576 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____582 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____582
      | FStar_Syntax_Syntax.U_max us ->
          let uu____585 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____585
let tag_with_range t s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> t
  | FStar_Pervasives_Native.Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____622 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____622
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____624 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____624
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___110_629 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.p = (uu___110_629.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___111_631 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___111_631.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___111_631.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___112_633 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___112_633.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___112_633.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match FStar_Pervasives_Native.snd s with
  | FStar_Pervasives_Native.None  -> l
  | FStar_Pervasives_Native.Some r ->
      let uu____663 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____663
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
      | uu____747 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____755 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____758 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____761 -> tag_with_range t0 s
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
               let uu____829 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____830 =
                 let uu____833 =
                   let uu____834 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____834 in
                 FStar_Syntax_Syntax.mk uu____833 in
               uu____830 FStar_Pervasives_Native.None uu____829
           | uu____846 ->
               let uu____847 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____847)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___108_858  ->
              match uu___108_858 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____862 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____862
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
      | uu____882 ->
          let uu___113_888 = t in
          let uu____889 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____893 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____896 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____899 =
            FStar_List.map
              (fun uu____917  ->
                 match uu____917 with
                 | (t1,imp) ->
                     let uu____932 = subst' s t1 in (uu____932, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____937 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____889;
            FStar_Syntax_Syntax.effect_name = uu____893;
            FStar_Syntax_Syntax.result_typ = uu____896;
            FStar_Syntax_Syntax.effect_args = uu____899;
            FStar_Syntax_Syntax.flags = uu____937
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
      | uu____959 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____975 = subst' s t1 in
               let uu____976 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____975 uu____976
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____989 = subst' s t1 in
               let uu____990 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____989 uu____990
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____996 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____996)
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
      | FStar_Syntax_Syntax.NT uu____1013 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1050 =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
      (FStar_List.map (shift_subst n1)) in
  (uu____1050, (FStar_Pervasives_Native.snd s))
let subst_binder' s uu____1075 =
  match uu____1075 with
  | (x,imp) ->
      let uu____1080 =
        let uu___114_1081 = x in
        let uu____1082 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___114_1081.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___114_1081.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1082
        } in
      (uu____1080, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1128 = shift_subst' i s in
               subst_binder' uu____1128 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg' s uu____1167 =
  match uu____1167 with
  | (t,imp) -> let uu____1178 = subst' s t in (uu____1178, imp)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1248 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1260 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1292  ->
                      fun uu____1293  ->
                        match (uu____1292, uu____1293) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1335 = aux n2 p2 in
                            (match uu____1335 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1260 with
             | (pats1,n2) ->
                 ((let uu___115_1367 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___115_1367.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_1382 = x in
              let uu____1383 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_1382.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_1382.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1383
              } in
            ((let uu___117_1388 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___117_1388.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___118_1398 = x in
              let uu____1399 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___118_1398.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___118_1398.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1399
              } in
            ((let uu___119_1404 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___119_1404.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___120_1419 = x in
              let uu____1420 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_1419.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_1419.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1420
              } in
            let t01 = subst' s1 t0 in
            ((let uu___121_1428 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___121_1428.FStar_Syntax_Syntax.p)
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
          let uu____1445 =
            let uu___122_1446 = rc in
            let uu____1447 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___122_1446.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1447;
              FStar_Syntax_Syntax.residual_flags =
                (uu___122_1446.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1445
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
        let uu____1475 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____1475 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1482 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1499 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1502 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1507 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1520 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1521 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1522 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____1534 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1534 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1555 =
            let uu____1556 =
              let uu____1566 = subst' s t0 in
              let uu____1569 = subst_args' s args in (uu____1566, uu____1569) in
            FStar_Syntax_Syntax.Tm_app uu____1556 in
          mk1 uu____1555
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1641 = subst' s t1 in FStar_Util.Inl uu____1641
            | FStar_Util.Inr c ->
                let uu____1655 = subst_comp' s c in FStar_Util.Inr uu____1655 in
          let uu____1662 =
            let uu____1663 =
              let uu____1681 = subst' s t0 in
              let uu____1684 =
                let uu____1696 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1696) in
              (uu____1681, uu____1684, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1663 in
          mk1 uu____1662
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1757 =
            let uu____1758 =
              let uu____1768 = subst_binders' s bs in
              let uu____1772 = subst' s' body in
              let uu____1775 = push_subst_lcomp s' lopt in
              (uu____1768, uu____1772, uu____1775) in
            FStar_Syntax_Syntax.Tm_abs uu____1758 in
          mk1 uu____1757
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1800 =
            let uu____1801 =
              let uu____1809 = subst_binders' s bs in
              let uu____1813 =
                let uu____1816 = shift_subst' n1 s in
                subst_comp' uu____1816 comp in
              (uu____1809, uu____1813) in
            FStar_Syntax_Syntax.Tm_arrow uu____1801 in
          mk1 uu____1800
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___123_1839 = x in
            let uu____1840 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_1839.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_1839.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1840
            } in
          let phi1 =
            let uu____1846 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____1846 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____1935  ->
                    match uu____1935 with
                    | (pat,wopt,branch) ->
                        let uu____1968 = subst_pat' s pat in
                        (match uu____1968 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2003 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2003 in
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
                      let uu____2071 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2071
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___124_2082 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_2082.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_2082.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___125_2084 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_2084.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_2084.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2103 =
            let uu____2104 =
              let uu____2109 = subst' s t0 in
              let uu____2112 =
                let uu____2113 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2113 in
              (uu____2109, uu____2112) in
            FStar_Syntax_Syntax.Tm_meta uu____2104 in
          mk1 uu____2103
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2155 =
            let uu____2156 =
              let uu____2161 = subst' s t0 in
              let uu____2164 =
                let uu____2165 =
                  let uu____2170 = subst' s t1 in (m, uu____2170) in
                FStar_Syntax_Syntax.Meta_monadic uu____2165 in
              (uu____2161, uu____2164) in
            FStar_Syntax_Syntax.Tm_meta uu____2156 in
          mk1 uu____2155
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2189 =
            let uu____2190 =
              let uu____2195 = subst' s t0 in
              let uu____2198 =
                let uu____2199 =
                  let uu____2205 = subst' s t1 in (m1, m2, uu____2205) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2199 in
              (uu____2195, uu____2198) in
            FStar_Syntax_Syntax.Tm_meta uu____2190 in
          mk1 uu____2189
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2218 =
            let uu____2219 = let uu____2224 = subst' s t1 in (uu____2224, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2219 in
          mk1 uu____2218
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____2269 = push_subst s t2 in compress uu____2269 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____2276 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2280 -> compress t'
         | uu____2295 -> t')
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
             (let uu___126_2324 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___126_2324.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____2345 =
      FStar_List.fold_right
        (fun uu____2360  ->
           fun uu____2361  ->
             match (uu____2360, uu____2361) with
             | ((x,uu____2376),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____2345 FStar_Pervasives_Native.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___127_2458 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2459 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___127_2458.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___127_2458.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2459
          } in
        let o1 =
          let uu____2464 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2464 in
        let uu____2466 = aux bs' o1 in
        (match uu____2466 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    let uu____2499 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____2499
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____2521 = open_binders' bs in
      match uu____2521 with
      | (bs',opening) ->
          let uu____2541 = subst opening t in (bs', uu____2541, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____2556 = open_term' bs t in
      match uu____2556 with | (b,t1,uu____2564) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____2575 = open_binders' bs in
      match uu____2575 with
      | (bs',opening) ->
          let uu____2594 = subst_comp opening t in (bs', uu____2594)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2642 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2658 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2710  ->
                    fun uu____2711  ->
                      match (uu____2710, uu____2711) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2788 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2788 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2658 with
           | (pats1,sub2,renaming1) ->
               ((let uu___128_2877 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_2877.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___129_2888 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2889 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_2888.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_2888.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2889
            } in
          let sub2 =
            let uu____2894 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2894 in
          ((let uu___130_2902 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___130_2902.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___131_2908 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2909 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_2908.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_2908.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2909
            } in
          let sub2 =
            let uu____2914 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2914 in
          ((let uu___132_2922 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___132_2922.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_2933 = x in
            let uu____2934 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_2933.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_2933.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2934
            } in
          let t01 = subst sub1 t0 in
          ((let uu___134_2944 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_2944.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____2946 = open_pat_aux [] [] p in
    match uu____2946 with | (p1,sub1,uu____2961) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____2977  ->
    match uu____2977 with
    | (p,wopt,e) ->
        let uu____2993 = open_pat p in
        (match uu____2993 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____3008 = subst opening w in
                   FStar_Pervasives_Native.Some uu____3008 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3019 = closing_subst bs in subst uu____3019 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3029 = closing_subst bs in subst_comp uu____3029 c
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
            let uu___135_3063 = x in
            let uu____3064 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_3063.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_3063.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3064
            } in
          let s' =
            let uu____3069 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3069 in
          let uu____3071 = aux s' tl1 in (x1, imp) :: uu____3071 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___136_3087 = lc in
      let uu____3088 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___136_3087.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3088;
        FStar_Syntax_Syntax.cflags =
          (uu___136_3087.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3093  ->
             let uu____3094 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3094)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3124 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3137 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3175  ->
                    fun uu____3176  ->
                      match (uu____3175, uu____3176) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3230 = aux sub2 p2 in
                          (match uu____3230 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3137 with
           | (pats1,sub2) ->
               ((let uu___137_3284 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___137_3284.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___138_3295 = x in
            let uu____3296 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_3295.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_3295.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3296
            } in
          let sub2 =
            let uu____3301 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3301 in
          ((let uu___139_3306 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___139_3306.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___140_3310 = x in
            let uu____3311 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3310.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_3310.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3311
            } in
          let sub2 =
            let uu____3316 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3316 in
          ((let uu___141_3321 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___141_3321.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_3330 = x in
            let uu____3331 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_3330.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_3330.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3331
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_3338 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___143_3338.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3343  ->
    match uu____3343 with
    | (p,wopt,e) ->
        let uu____3359 = close_pat p in
        (match uu____3359 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____3380 = subst closing w in
                   FStar_Pervasives_Native.Some uu____3380 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3399 =
      let uu____3404 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (FStar_Pervasives_Native.Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3404 FStar_List.unzip in
    match uu____3399 with | (s,us') -> (s, us')
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
      let uu____3467 = univ_var_opening us in
      match uu____3467 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____3494 = univ_var_opening us in
      match uu____3494 with
      | (s,us') -> let uu____3507 = subst_comp s c in (us', uu____3507)
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
      let uu____3554 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3554
      then (lbs, t)
      else
        (let uu____3560 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3578  ->
                  match uu____3578 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3597 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3597 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___144_3601 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___144_3601.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___144_3601.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___144_3601.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___144_3601.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3560 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3626 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3644  ->
                                match uu____3644 with
                                | (i,us,out) ->
                                    let u1 =
                                      FStar_Syntax_Syntax.new_univ_name
                                        FStar_Pervasives_Native.None in
                                    ((i + (Prims.parse_int "1")), (u1 :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i,
                                            (FStar_Syntax_Syntax.U_name u1)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening) in
                       match uu____3626 with
                       | (uu____3667,us,u_let_rec_opening) ->
                           let uu___145_3674 = lb in
                           let uu____3675 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___145_3674.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___145_3674.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___145_3674.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3675
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
      let uu____3693 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3693
      then (lbs, t)
      else
        (let uu____3699 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3712  ->
                  match uu____3712 with
                  | (i,out) ->
                      let uu____3723 =
                        let uu____3725 =
                          let uu____3726 =
                            let uu____3729 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3729, i) in
                          FStar_Syntax_Syntax.NM uu____3726 in
                        uu____3725 :: out in
                      ((i + (Prims.parse_int "1")), uu____3723)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3699 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3750 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3762  ->
                                match uu____3762 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____3750 with
                       | (uu____3775,u_let_rec_closing) ->
                           let uu___146_3779 = lb in
                           let uu____3780 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___146_3779.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___146_3779.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___146_3779.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___146_3779.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3780
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun binders  ->
    fun uu____3792  ->
      match uu____3792 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3818  ->
                   match uu____3818 with
                   | (x,uu____3822) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun uu____3838  ->
      match uu____3838 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____3865 = subst s t in (us', uu____3865)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3888  ->
              match uu____3888 with
              | (x,uu____3892) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  -> closing_subst bs