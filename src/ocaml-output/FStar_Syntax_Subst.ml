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
let map_some_curry f x uu___100_101 =
  match uu___100_101 with | None  -> x | Some (a,b) -> f a b
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
        let uu____360 = FStar_Unionfind.find uv in
        (match uu____360 with
         | FStar_Syntax_Syntax.Fixed t' -> force_uvar' t'
         | uu____374 -> t)
    | uu____378 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____391 = FStar_Util.physical_equality t t' in
    if uu____391
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
        let uu____450 = FStar_ST.read m in
        (match uu____450 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____486 = c () in force_delayed_thunk uu____486 in
                  (FStar_ST.write m (Some t'); t')
              | uu____497 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____529 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____536 = FStar_Unionfind.find u' in
        (match uu____536 with | Some u1 -> compress_univ u1 | uu____540 -> u)
    | uu____542 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_552  ->
           match uu___101_552 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____556 =
                 let uu____557 =
                   let uu____558 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____558 in
                 FStar_Syntax_Syntax.bv_to_name uu____557 in
               Some uu____556
           | uu____559 -> None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_569  ->
           match uu___102_569 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____573 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___107_574 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___107_574.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___107_574.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____573
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____583 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_593  ->
           match uu___103_593 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____597 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_607  ->
           match uu___104_607 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____611 -> None)
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
      | FStar_Syntax_Syntax.U_unif uu____627 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____631 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____631
      | FStar_Syntax_Syntax.U_max us ->
          let uu____634 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____634
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____667 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____667
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____669 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____669
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___108_677 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___108_677.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___108_677.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___109_693 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___109_693.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___109_693.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___110_695 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___110_695.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___110_695.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____722 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____722
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
      | uu____804 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____812 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____815 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____818 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____899,uu____900) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____956 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____957 =
                 let uu____960 =
                   let uu____961 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____961 in
                 FStar_Syntax_Syntax.mk uu____960 in
               uu____957 None uu____956
           | uu____973 ->
               let uu____974 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____974)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___105_988  ->
              match uu___105_988 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____992 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____992
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
      | uu____1012 ->
          let uu___111_1018 = t in
          let uu____1019 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1023 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1026 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1029 =
            FStar_List.map
              (fun uu____1043  ->
                 match uu____1043 with
                 | (t1,imp) ->
                     let uu____1058 = subst' s t1 in (uu____1058, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1063 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1019;
            FStar_Syntax_Syntax.effect_name = uu____1023;
            FStar_Syntax_Syntax.result_typ = uu____1026;
            FStar_Syntax_Syntax.effect_args = uu____1029;
            FStar_Syntax_Syntax.flags = uu____1063
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
      | uu____1085 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1101 = subst' s t1 in
               let uu____1102 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1101 uu____1102
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1115 = subst' s t1 in
               let uu____1116 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1115 uu____1116
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1122 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1122)
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
      | FStar_Syntax_Syntax.NT uu____1137 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1169 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1169, (snd s))
let subst_binder' s uu____1191 =
  match uu____1191 with
  | (x,imp) ->
      let uu____1196 =
        let uu___112_1197 = x in
        let uu____1198 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___112_1197.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___112_1197.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1198
        } in
      (uu____1196, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1239 = shift_subst' i s in
               subst_binder' uu____1239 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1273 =
  match uu____1273 with
  | (t,imp) -> let uu____1284 = subst' s t in (uu____1284, imp)
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
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: empty disjunction"
        | FStar_Syntax_Syntax.Pat_constant uu____1359 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
            let uu____1371 = aux n1 p2 in
            (match uu____1371 with
             | (p3,m) ->
                 let ps1 =
                   FStar_List.map
                     (fun p4  -> let uu____1385 = aux n1 p4 in fst uu____1385)
                     ps in
                 ((let uu___113_1390 = p3 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                     FStar_Syntax_Syntax.ty =
                       (uu___113_1390.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___113_1390.FStar_Syntax_Syntax.p)
                   }), m))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1403 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1428  ->
                      fun uu____1429  ->
                        match (uu____1428, uu____1429) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1476 = aux n2 p2 in
                            (match uu____1476 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1403 with
             | (pats1,n2) ->
                 ((let uu___114_1508 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___114_1508.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___114_1508.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___115_1524 = x in
              let uu____1525 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1524.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1524.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1525
              } in
            ((let uu___116_1530 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1530.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1530.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___117_1541 = x in
              let uu____1542 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1541.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1541.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1542
              } in
            ((let uu___118_1547 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___118_1547.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1547.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___119_1563 = x in
              let uu____1564 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1563.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1563.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1564
              } in
            let t01 = subst' s1 t0 in
            ((let uu___120_1572 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___120_1572.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___120_1572.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None  -> lopt
  | Some (FStar_Util.Inr uu____1600) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1606 =
        let uu____1609 =
          let uu___121_1610 = l in
          let uu____1611 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___121_1610.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1611;
            FStar_Syntax_Syntax.cflags =
              (uu___121_1610.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1614  ->
                 let uu____1615 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1615)
          } in
        FStar_Util.Inl uu____1609 in
      Some uu____1606
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
        let uu____1638 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1638 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1645 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1668 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1671 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1676 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1687 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1688 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1689 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1701 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1701 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1722 =
            let uu____1723 =
              let uu____1733 = subst' s t0 in
              let uu____1736 = subst_args' s args in (uu____1733, uu____1736) in
            FStar_Syntax_Syntax.Tm_app uu____1723 in
          mk1 uu____1722
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1808 = subst' s t1 in FStar_Util.Inl uu____1808
            | FStar_Util.Inr c ->
                let uu____1822 = subst_comp' s c in FStar_Util.Inr uu____1822 in
          let uu____1829 =
            let uu____1830 =
              let uu____1848 = subst' s t0 in
              let uu____1851 =
                let uu____1863 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1863) in
              (uu____1848, uu____1851, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1830 in
          mk1 uu____1829
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1931 =
            let uu____1932 =
              let uu____1947 = subst_binders' s bs in
              let uu____1951 = subst' s' body in
              let uu____1954 = push_subst_lcomp s' lopt in
              (uu____1947, uu____1951, uu____1954) in
            FStar_Syntax_Syntax.Tm_abs uu____1932 in
          mk1 uu____1931
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1991 =
            let uu____1992 =
              let uu____2000 = subst_binders' s bs in
              let uu____2004 =
                let uu____2007 = shift_subst' n1 s in
                subst_comp' uu____2007 comp in
              (uu____2000, uu____2004) in
            FStar_Syntax_Syntax.Tm_arrow uu____1992 in
          mk1 uu____1991
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___122_2028 = x in
            let uu____2029 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_2028.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_2028.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2029
            } in
          let phi1 =
            let uu____2035 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2035 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2118  ->
                    match uu____2118 with
                    | (pat,wopt,branch) ->
                        let uu____2154 = subst_pat' s pat in
                        (match uu____2154 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2189 = subst' s1 w in
                                   Some uu____2189 in
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
                      let uu____2249 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2249
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_2259 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2259.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2259.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___124_2261 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___125_2262 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___125_2262.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___125_2262.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___124_2261.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___124_2261.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___126_2277 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___126_2277.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___126_2277.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2296 =
            let uu____2297 =
              let uu____2302 = subst' s t0 in
              let uu____2305 =
                let uu____2306 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2306 in
              (uu____2302, uu____2305) in
            FStar_Syntax_Syntax.Tm_meta uu____2297 in
          mk1 uu____2296
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2348 =
            let uu____2349 =
              let uu____2354 = subst' s t0 in
              let uu____2357 =
                let uu____2358 =
                  let uu____2363 = subst' s t1 in (m, uu____2363) in
                FStar_Syntax_Syntax.Meta_monadic uu____2358 in
              (uu____2354, uu____2357) in
            FStar_Syntax_Syntax.Tm_meta uu____2349 in
          mk1 uu____2348
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2382 =
            let uu____2383 =
              let uu____2388 = subst' s t0 in
              let uu____2391 =
                let uu____2392 =
                  let uu____2398 = subst' s t1 in (m1, m2, uu____2398) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2392 in
              (uu____2388, uu____2391) in
            FStar_Syntax_Syntax.Tm_meta uu____2383 in
          mk1 uu____2382
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2411 =
            let uu____2412 = let uu____2417 = subst' s t1 in (uu____2417, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2412 in
          mk1 uu____2411
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2480 = push_subst s t2 in compress uu____2480 in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2487 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2491 -> compress t'
         | uu____2512 -> t')
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
             (let uu___127_2536 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___127_2536.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2564 =
    FStar_List.fold_right
      (fun uu____2573  ->
         fun uu____2574  ->
           match (uu____2573, uu____2574) with
           | ((x,uu____2589),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2564 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___128_2669 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2670 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___128_2669.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___128_2669.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2670
          } in
        let o1 =
          let uu____2675 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2675 in
        let uu____2677 = aux bs' o1 in
        (match uu____2677 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2709 = open_binders' bs in fst uu____2709
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2729 = open_binders' bs in
      match uu____2729 with
      | (bs',opening) ->
          let uu____2749 = subst opening t in (bs', uu____2749, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2762 = open_term' bs t in
      match uu____2762 with | (b,t1,uu____2770) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2779 = open_binders' bs in
      match uu____2779 with
      | (bs',opening) ->
          let uu____2798 = subst_comp opening t in (bs', uu____2798)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_open_pat_disj sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2835 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2841 -> p1
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___129_2854 = p1 in
          let uu____2857 =
            let uu____2858 =
              let uu____2866 =
                FStar_All.pipe_right pats
                  (FStar_List.map
                     (fun uu____2890  ->
                        match uu____2890 with
                        | (p2,b) ->
                            let uu____2905 =
                              aux_open_pat_disj sub1 renaming p2 in
                            (uu____2905, b))) in
              (fv, uu____2866) in
            FStar_Syntax_Syntax.Pat_cons uu____2858 in
          {
            FStar_Syntax_Syntax.v = uu____2857;
            FStar_Syntax_Syntax.ty = (uu___129_2854.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___129_2854.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___106_2920  ->
                 match uu___106_2920 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2926 -> None) in
          let y =
            match yopt with
            | None  ->
                let uu___130_2930 = FStar_Syntax_Syntax.freshen_bv x in
                let uu____2931 = subst sub1 x.FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___130_2930.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___130_2930.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____2931
                }
            | Some y -> y in
          let uu___131_2935 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___131_2935.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___131_2935.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___132_2940 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2941 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_2940.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_2940.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2941
            } in
          let uu___133_2944 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___133_2944.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___133_2944.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___134_2954 = x in
            let uu____2955 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_2954.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_2954.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2955
            } in
          let t01 = subst sub1 t0 in
          let uu___135_2959 = p1 in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
            FStar_Syntax_Syntax.ty = (uu___135_2959.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___135_2959.FStar_Syntax_Syntax.p)
          } in
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____3013 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3029 = open_pat_aux sub1 renaming p2 in
          (match uu____3029 with
           | (p3,sub2,renaming1) ->
               let ps1 = FStar_List.map (aux_open_pat_disj sub2 renaming1) ps in
               ((let uu___136_3077 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___136_3077.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___136_3077.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3094 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3140  ->
                    fun uu____3141  ->
                      match (uu____3140, uu____3141) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____3229 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____3229 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3094 with
           | (pats1,sub2,renaming1) ->
               ((let uu___137_3330 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___137_3330.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___137_3330.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___138_3344 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3345 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_3344.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_3344.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3345
            } in
          let sub2 =
            let uu____3350 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3350 in
          ((let uu___139_3358 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___139_3358.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_3358.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___140_3365 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3366 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3365.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_3365.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3366
            } in
          let sub2 =
            let uu____3371 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3371 in
          ((let uu___141_3379 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___141_3379.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_3379.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_3391 = x in
            let uu____3392 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_3391.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_3391.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3392
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_3402 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___143_3402.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___143_3402.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3405 = open_pat_aux [] [] p in
    match uu____3405 with | (p1,sub1,uu____3421) -> (p1, sub1)
let find_map_i f l =
  let rec aux i l1 =
    match l1 with
    | [] -> None
    | hd1::tl1 ->
        let uu____3480 = f i hd1 in
        (match uu____3480 with
         | None  -> aux (i + (Prims.parse_int "1")) tl1
         | Some b -> Some b) in
  aux (Prims.parse_int "0") l
let permute_disjunctive_pattern first case l =
  let uu____3504 =
    let uu____3507 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_disj [first; case])
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n FStar_Range.dummyRange in
    open_pat uu____3507 in
  match uu____3504 with
  | (p,uu____3510) ->
      let uu____3511 =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj (first1::case1::[]) ->
            let uu____3532 = FStar_Syntax_Syntax.pat_bvs first1 in
            let uu____3534 = FStar_Syntax_Syntax.pat_bvs case1 in
            (uu____3532, uu____3534)
        | uu____3538 -> failwith "Impossible" in
      (match uu____3511 with
       | (first_vars,case_vars) ->
           (if (FStar_List.length l) <> (FStar_List.length first_vars)
            then failwith "Unexpected length of matched pattern variables"
            else ();
            FStar_All.pipe_right first_vars
              (FStar_List.map
                 (fun v1  ->
                    let found =
                      find_map_i
                        (fun i  ->
                           fun u  ->
                             if FStar_Syntax_Syntax.bv_eq u v1
                             then Some i
                             else None) case_vars in
                    match found with
                    | None  ->
                        failwith
                          "Impossible: unequal variables in disjunctive pattern"
                    | Some i -> FStar_List.nth l i))))
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3568  ->
    match uu____3568 with
    | (p,wopt,e) ->
        let uu____3586 = open_pat p in
        (match uu____3586 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3601 = subst opening w in Some uu____3601 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3610 = closing_subst bs in subst uu____3610 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3618 = closing_subst bs in subst_comp uu____3618 c
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
            let uu___144_3651 = x in
            let uu____3652 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___144_3651.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_3651.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3652
            } in
          let s' =
            let uu____3657 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3657 in
          let uu____3659 = aux s' tl1 in (x1, imp) :: uu____3659 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___145_3673 = lc in
      let uu____3674 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___145_3673.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3674;
        FStar_Syntax_Syntax.cflags =
          (uu___145_3673.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3677  ->
             let uu____3678 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3678)
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
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____3721 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3734 = aux sub1 p2 in
          (match uu____3734 with
           | (p3,sub2) ->
               let ps1 =
                 FStar_List.map
                   (fun p4  -> let uu____3764 = aux sub2 p4 in fst uu____3764)
                   ps in
               ((let uu___146_3776 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___146_3776.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___146_3776.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3793 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3827  ->
                    fun uu____3828  ->
                      match (uu____3827, uu____3828) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3893 = aux sub2 p2 in
                          (match uu____3893 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3793 with
           | (pats1,sub2) ->
               ((let uu___147_3959 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___147_3959.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___147_3959.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___148_3973 = x in
            let uu____3974 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_3973.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_3973.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3974
            } in
          let sub2 =
            let uu____3979 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3979 in
          ((let uu___149_3984 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___149_3984.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___149_3984.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___150_3989 = x in
            let uu____3990 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___150_3989.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___150_3989.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3990
            } in
          let sub2 =
            let uu____3995 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3995 in
          ((let uu___151_4000 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___151_4000.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___151_4000.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___152_4010 = x in
            let uu____4011 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___152_4010.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___152_4010.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4011
            } in
          let t01 = subst sub1 t0 in
          ((let uu___153_4018 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___153_4018.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___153_4018.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4023  ->
    match uu____4023 with
    | (p,wopt,e) ->
        let uu____4041 = close_pat p in
        (match uu____4041 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____4065 = subst closing w in Some uu____4065 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____4081 =
      let uu____4086 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____4086 FStar_List.unzip in
    match uu____4081 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____4127 = univ_var_opening us in
      match uu____4127 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____4152 = univ_var_opening us in
      match uu____4152 with
      | (s,us') -> let uu____4165 = subst_comp s c in (us', uu____4165)
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
      let uu____4208 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4208
      then (lbs, t)
      else
        (let uu____4214 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4226  ->
                  match uu____4226 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____4245 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____4245 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___154_4248 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___154_4248.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___154_4248.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___154_4248.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___154_4248.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____4214 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4266 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4278  ->
                                match uu____4278 with
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
                       match uu____4266 with
                       | (uu____4301,us,u_let_rec_opening) ->
                           let uu___155_4308 = lb in
                           let uu____4309 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___155_4308.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___155_4308.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_4308.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4309
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____4325 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4325
      then (lbs, t)
      else
        (let uu____4331 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4339  ->
                  match uu____4339 with
                  | (i,out) ->
                      let uu____4350 =
                        let uu____4352 =
                          let uu____4353 =
                            let uu____4356 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____4356, i) in
                          FStar_Syntax_Syntax.NM uu____4353 in
                        uu____4352 :: out in
                      ((i + (Prims.parse_int "1")), uu____4350)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____4331 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4371 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4379  ->
                                match uu____4379 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____4371 with
                       | (uu____4392,u_let_rec_closing) ->
                           let uu___156_4396 = lb in
                           let uu____4397 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___156_4396.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___156_4396.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___156_4396.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_4396.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4397
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____4407  ->
      match uu____4407 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____4425  ->
                   match uu____4425 with
                   | (x,uu____4429) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4440  ->
      match uu____4440 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____4458 = subst s t in (us', uu____4458)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4473  ->
              match uu____4473 with
              | (x,uu____4477) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))