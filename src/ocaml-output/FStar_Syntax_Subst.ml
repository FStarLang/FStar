open Prims
let subst_to_string s =
  let uu____14 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____22  ->
            match uu____22 with
            | (b,uu____26) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____14 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> None
  | s0::rest ->
      let uu____61 = f s0 in
      (match uu____61 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
let map_some_curry f x uu___107_101 =
  match uu___107_101 with | None  -> x | Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____162 = apply_until_some f s in
  FStar_All.pipe_right uu____162 (map_some_curry g t)
let compose_subst s1 s2 =
  let s = FStar_List.append (fst s1) (fst s2) in
  let ropt =
    match snd s2 with | Some uu____217 -> snd s2 | uu____220 -> snd s1 in
  (s, ropt)
let delay:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
      option) -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed
            (FStar_Util.Inl (t', (compose_subst s' s)))
            t.FStar_Syntax_Syntax.pos
      | uu____316 ->
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
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____347) ->
        let uu____360 = FStar_Syntax_Unionfind.find uv in
        (match uu____360 with | Some t' -> force_uvar' t' | uu____365 -> t)
    | uu____367 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____380 = FStar_Util.physical_equality t t' in
    if uu____380
    then t
    else delay t' ([], (Some (t.FStar_Syntax_Syntax.pos)))
let rec force_delayed_thunk:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____439 = FStar_ST.read m in
        (match uu____439 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____475 = c () in force_delayed_thunk uu____475 in
                  (FStar_ST.write m (Some t'); t')
              | uu____486 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____518 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____525 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____525 with | Some u1 -> compress_univ u1 | uu____528 -> u)
    | uu____530 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___108_540  ->
           match uu___108_540 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____544 =
                 let uu____545 =
                   let uu____546 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____546 in
                 FStar_Syntax_Syntax.bv_to_name uu____545 in
               Some uu____544
           | uu____547 -> None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___109_557  ->
           match uu___109_557 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____561 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___113_562 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_562.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___113_562.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____561
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____571 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___110_581  ->
           match uu___110_581 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____585 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___111_595  ->
           match uu___111_595 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____599 -> None)
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
      | FStar_Syntax_Syntax.U_unif uu____615 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____619 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____619
      | FStar_Syntax_Syntax.U_max us ->
          let uu____622 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____622
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____655 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____655
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____657 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____657
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___114_665 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___114_665.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___114_665.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___115_681 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___115_681.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___115_681.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___116_683 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___116_683.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___116_683.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____710 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____710
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match snd s with
      | None  -> r
      | Some r' -> FStar_Range.set_use_range r r'
let rec subst':
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (snd s)) in
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____792 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____800 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____803 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____806 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____887,uu____888) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____944 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____945 =
                 let uu____948 =
                   let uu____949 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____949 in
                 FStar_Syntax_Syntax.mk uu____948 in
               uu____945 None uu____944
           | uu____961 ->
               let uu____962 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____962)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___112_976  ->
              match uu___112_976 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____980 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____980
              | f -> f))
and subst_comp_typ':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
    option) -> FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____1000 ->
          let uu___117_1006 = t in
          let uu____1007 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1011 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1014 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1017 =
            FStar_List.map
              (fun uu____1031  ->
                 match uu____1031 with
                 | (t1,imp) ->
                     let uu____1046 = subst' s t1 in (uu____1046, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1051 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1007;
            FStar_Syntax_Syntax.effect_name = uu____1011;
            FStar_Syntax_Syntax.result_typ = uu____1014;
            FStar_Syntax_Syntax.effect_args = uu____1017;
            FStar_Syntax_Syntax.flags = uu____1051
          }
and subst_comp':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
    option) ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None ) -> t
      | ([]::[],None ) -> t
      | uu____1073 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1089 = subst' s t1 in
               let uu____1090 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1089 uu____1090
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1103 = subst' s t1 in
               let uu____1104 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1103 uu____1104
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1110 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1110)
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
      | FStar_Syntax_Syntax.NT uu____1125 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1157 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1157, (snd s))
let subst_binder' s uu____1179 =
  match uu____1179 with
  | (x,imp) ->
      let uu____1184 =
        let uu___118_1185 = x in
        let uu____1186 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___118_1185.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___118_1185.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1186
        } in
      (uu____1184, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1227 = shift_subst' i s in
               subst_binder' uu____1227 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1261 =
  match uu____1261 with
  | (t,imp) -> let uu____1272 = subst' s t in (uu____1272, imp)
let subst_args' s = FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list* FStar_Range.range option) ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t -> (FStar_Syntax_Syntax.pat* Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1343 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1358 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1383  ->
                      fun uu____1384  ->
                        match (uu____1383, uu____1384) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1431 = aux n2 p2 in
                            (match uu____1431 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1358 with
             | (pats1,n2) ->
                 ((let uu___119_1463 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___119_1463.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___119_1463.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___120_1479 = x in
              let uu____1480 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_1479.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_1479.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1480
              } in
            ((let uu___121_1485 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___121_1485.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___121_1485.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___122_1496 = x in
              let uu____1497 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___122_1496.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___122_1496.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1497
              } in
            ((let uu___123_1502 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___123_1502.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___123_1502.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___124_1518 = x in
              let uu____1519 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___124_1518.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___124_1518.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1519
              } in
            let t01 = subst' s1 t0 in
            ((let uu___125_1527 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___125_1527.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___125_1527.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None  -> lopt
  | Some (FStar_Util.Inr uu____1555) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1561 =
        let uu____1564 =
          let uu___126_1565 = l in
          let uu____1566 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___126_1565.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1566;
            FStar_Syntax_Syntax.cflags =
              (uu___126_1565.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1569  ->
                 let uu____1570 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1570)
          } in
        FStar_Util.Inl uu____1564 in
      Some uu____1561
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
        let uu____1593 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1593 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1600 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1623 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1626 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1631 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1642 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1643 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1644 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1656 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1656 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1677 =
            let uu____1678 =
              let uu____1688 = subst' s t0 in
              let uu____1691 = subst_args' s args in (uu____1688, uu____1691) in
            FStar_Syntax_Syntax.Tm_app uu____1678 in
          mk1 uu____1677
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1763 = subst' s t1 in FStar_Util.Inl uu____1763
            | FStar_Util.Inr c ->
                let uu____1777 = subst_comp' s c in FStar_Util.Inr uu____1777 in
          let uu____1784 =
            let uu____1785 =
              let uu____1803 = subst' s t0 in
              let uu____1806 =
                let uu____1818 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1818) in
              (uu____1803, uu____1806, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1785 in
          mk1 uu____1784
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1886 =
            let uu____1887 =
              let uu____1902 = subst_binders' s bs in
              let uu____1906 = subst' s' body in
              let uu____1909 = push_subst_lcomp s' lopt in
              (uu____1902, uu____1906, uu____1909) in
            FStar_Syntax_Syntax.Tm_abs uu____1887 in
          mk1 uu____1886
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1946 =
            let uu____1947 =
              let uu____1955 = subst_binders' s bs in
              let uu____1959 =
                let uu____1962 = shift_subst' n1 s in
                subst_comp' uu____1962 comp in
              (uu____1955, uu____1959) in
            FStar_Syntax_Syntax.Tm_arrow uu____1947 in
          mk1 uu____1946
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___127_1983 = x in
            let uu____1984 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_1983.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_1983.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1984
            } in
          let phi1 =
            let uu____1990 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____1990 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2073  ->
                    match uu____2073 with
                    | (pat,wopt,branch) ->
                        let uu____2109 = subst_pat' s pat in
                        (match uu____2109 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2144 = subst' s1 w in
                                   Some uu____2144 in
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
                      let uu____2204 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2204
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___128_2214 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___128_2214.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___128_2214.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___129_2216 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___130_2217 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___130_2217.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___130_2217.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___129_2216.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___129_2216.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___131_2232 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___131_2232.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___131_2232.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2251 =
            let uu____2252 =
              let uu____2257 = subst' s t0 in
              let uu____2260 =
                let uu____2261 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2261 in
              (uu____2257, uu____2260) in
            FStar_Syntax_Syntax.Tm_meta uu____2252 in
          mk1 uu____2251
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2303 =
            let uu____2304 =
              let uu____2309 = subst' s t0 in
              let uu____2312 =
                let uu____2313 =
                  let uu____2318 = subst' s t1 in (m, uu____2318) in
                FStar_Syntax_Syntax.Meta_monadic uu____2313 in
              (uu____2309, uu____2312) in
            FStar_Syntax_Syntax.Tm_meta uu____2304 in
          mk1 uu____2303
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2337 =
            let uu____2338 =
              let uu____2343 = subst' s t0 in
              let uu____2346 =
                let uu____2347 =
                  let uu____2353 = subst' s t1 in (m1, m2, uu____2353) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2347 in
              (uu____2343, uu____2346) in
            FStar_Syntax_Syntax.Tm_meta uu____2338 in
          mk1 uu____2337
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2366 =
            let uu____2367 = let uu____2372 = subst' s t1 in (uu____2372, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2367 in
          mk1 uu____2366
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2435 = push_subst s t2 in compress uu____2435 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2442 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2446 -> compress t'
         | uu____2467 -> t')
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst' ([s], None) t
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
          (Some
             (let uu___132_2491 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___132_2491.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2519 =
    FStar_List.fold_right
      (fun uu____2528  ->
         fun uu____2529  ->
           match (uu____2528, uu____2529) with
           | ((x,uu____2544),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2519 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___133_2624 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2625 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___133_2624.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___133_2624.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2625
          } in
        let o1 =
          let uu____2630 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2630 in
        let uu____2632 = aux bs' o1 in
        (match uu____2632 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2664 = open_binders' bs in fst uu____2664
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2684 = open_binders' bs in
      match uu____2684 with
      | (bs',opening) ->
          let uu____2704 = subst opening t in (bs', uu____2704, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2717 = open_term' bs t in
      match uu____2717 with | (b,t1,uu____2725) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2734 = open_binders' bs in
      match uu____2734 with
      | (bs',opening) ->
          let uu____2753 = subst_comp opening t in (bs', uu____2753)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2804 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2823 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2869  ->
                    fun uu____2870  ->
                      match (uu____2869, uu____2870) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2958 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2958 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2823 with
           | (pats1,sub2,renaming1) ->
               ((let uu___134_3059 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___134_3059.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___134_3059.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___135_3073 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3074 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_3073.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_3073.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3074
            } in
          let sub2 =
            let uu____3079 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3079 in
          ((let uu___136_3087 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___136_3087.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___136_3087.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___137_3094 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3095 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___137_3094.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___137_3094.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3095
            } in
          let sub2 =
            let uu____3100 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3100 in
          ((let uu___138_3108 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___138_3108.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___138_3108.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___139_3120 = x in
            let uu____3121 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3120.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3120.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3121
            } in
          let t01 = subst sub1 t0 in
          ((let uu___140_3131 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___140_3131.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___140_3131.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3134 = open_pat_aux [] [] p in
    match uu____3134 with | (p1,sub1,uu____3150) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3168  ->
    match uu____3168 with
    | (p,wopt,e) ->
        let uu____3186 = open_pat p in
        (match uu____3186 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3201 = subst opening w in Some uu____3201 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3210 = closing_subst bs in subst uu____3210 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3218 = closing_subst bs in subst_comp uu____3218 c
let close_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___141_3251 = x in
            let uu____3252 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3251.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3251.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3252
            } in
          let s' =
            let uu____3257 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3257 in
          let uu____3259 = aux s' tl1 in (x1, imp) :: uu____3259 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___142_3273 = lc in
      let uu____3274 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___142_3273.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3274;
        FStar_Syntax_Syntax.cflags =
          (uu___142_3273.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3277  ->
             let uu____3278 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3278)
      }
let close_pat:
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t* FStar_Syntax_Syntax.subst_elt
      Prims.list)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3314 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3330 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3364  ->
                    fun uu____3365  ->
                      match (uu____3364, uu____3365) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3430 = aux sub2 p2 in
                          (match uu____3430 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3330 with
           | (pats1,sub2) ->
               ((let uu___143_3496 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___143_3496.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___143_3496.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___144_3510 = x in
            let uu____3511 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___144_3510.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_3510.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3511
            } in
          let sub2 =
            let uu____3516 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3516 in
          ((let uu___145_3521 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___145_3521.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___145_3521.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___146_3526 = x in
            let uu____3527 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_3526.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___146_3526.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3527
            } in
          let sub2 =
            let uu____3532 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3532 in
          ((let uu___147_3537 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___147_3537.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___147_3537.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___148_3547 = x in
            let uu____3548 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_3547.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_3547.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3548
            } in
          let t01 = subst sub1 t0 in
          ((let uu___149_3555 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___149_3555.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___149_3555.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3560  ->
    match uu____3560 with
    | (p,wopt,e) ->
        let uu____3578 = close_pat p in
        (match uu____3578 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3602 = subst closing w in Some uu____3602 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3618 =
      let uu____3623 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3623 FStar_List.unzip in
    match uu____3618 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3664 = univ_var_opening us in
      match uu____3664 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3689 = univ_var_opening us in
      match uu____3689 with
      | (s,us') -> let uu____3702 = subst_comp s c in (us', uu____3702)
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
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3745 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3745
      then (lbs, t)
      else
        (let uu____3751 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3763  ->
                  match uu____3763 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3782 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3782 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___150_3785 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___150_3785.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___150_3785.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___150_3785.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___150_3785.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3751 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3803 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3815  ->
                                match uu____3815 with
                                | (i,us,out) ->
                                    let u1 =
                                      FStar_Syntax_Syntax.new_univ_name None in
                                    ((i + (Prims.parse_int "1")), (u1 :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i,
                                            (FStar_Syntax_Syntax.U_name u1)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening) in
                       match uu____3803 with
                       | (uu____3838,us,u_let_rec_opening) ->
                           let uu___151_3845 = lb in
                           let uu____3846 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___151_3845.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___151_3845.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___151_3845.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3846
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3862 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3862
      then (lbs, t)
      else
        (let uu____3868 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3876  ->
                  match uu____3876 with
                  | (i,out) ->
                      let uu____3887 =
                        let uu____3889 =
                          let uu____3890 =
                            let uu____3893 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3893, i) in
                          FStar_Syntax_Syntax.NM uu____3890 in
                        uu____3889 :: out in
                      ((i + (Prims.parse_int "1")), uu____3887)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3868 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3908 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3916  ->
                                match uu____3916 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____3908 with
                       | (uu____3929,u_let_rec_closing) ->
                           let uu___152_3933 = lb in
                           let uu____3934 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___152_3933.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___152_3933.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___152_3933.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___152_3933.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3934
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3944  ->
      match uu____3944 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3962  ->
                   match uu____3962 with
                   | (x,uu____3966) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3977  ->
      match uu____3977 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____3995 = subst s t in (us', uu____3995)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4010  ->
              match uu____4010 with
              | (x,uu____4014) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))