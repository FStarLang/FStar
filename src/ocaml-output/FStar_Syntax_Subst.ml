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
let map_some_curry f x uu___102_101 =
  match uu___102_101 with | None  -> x | Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____162 = apply_until_some f s in
  FStar_All.pipe_right uu____162 (map_some_curry g t)
let compose_subst s1 s2 =
  let s = FStar_List.append (Prims.fst s1) (Prims.fst s2) in
  let ropt =
    match Prims.snd s2 with
    | Some uu____217 -> Prims.snd s2
    | uu____220 -> Prims.snd s1 in
  (s, ropt)
let delay:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
      Prims.option) -> FStar_Syntax_Syntax.term
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
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_552  ->
           match uu___103_552 with
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
      FStar_Syntax_Syntax.term Prims.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_569  ->
           match uu___104_569 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____573 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_574 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_574.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_574.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____573
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____583 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_593  ->
           match uu___105_593 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____597 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe Prims.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_607  ->
           match uu___106_607 with
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
      | FStar_Syntax_Syntax.U_zero 
        |FStar_Syntax_Syntax.U_unknown |FStar_Syntax_Syntax.U_unif _ -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____629 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____629
      | FStar_Syntax_Syntax.U_max us ->
          let uu____632 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____632
let tag_with_range t s =
  match Prims.snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____665 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____665
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____667 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____667
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___110_675 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___110_675.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___110_675.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___111_691 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___111_691.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___111_691.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___112_693 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___112_693.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___112_693.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match Prims.snd s with
  | None  -> l
  | Some r ->
      let uu____720 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____720
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match Prims.snd s with
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
      let subst_tail tl1 = subst' (tl1, (Prims.snd s)) in
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____802 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown 
             |FStar_Syntax_Syntax.Tm_constant _
              |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_uvar _ ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____883,uu____884) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (Prims.fst s)
                 subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____940 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____941 =
                 let uu____944 =
                   let uu____945 = subst_univ (Prims.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____945 in
                 FStar_Syntax_Syntax.mk uu____944 in
               uu____941 None uu____940
           | uu____957 ->
               let uu____958 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____958)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___107_972  ->
              match uu___107_972 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____976 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____976
              | f -> f))
and subst_comp_typ':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
    Prims.option) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____996 ->
          let uu___113_1002 = t in
          let uu____1003 =
            FStar_List.map (subst_univ (Prims.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1007 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1010 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1013 =
            FStar_List.map
              (fun uu____1027  ->
                 match uu____1027 with
                 | (t1,imp) ->
                     let uu____1042 = subst' s t1 in (uu____1042, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1047 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1003;
            FStar_Syntax_Syntax.effect_name = uu____1007;
            FStar_Syntax_Syntax.result_typ = uu____1010;
            FStar_Syntax_Syntax.effect_args = uu____1013;
            FStar_Syntax_Syntax.flags = uu____1047
          }
and subst_comp':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list* FStar_Range.range
    Prims.option) ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],None )|([]::[],None ) -> t
      | uu____1069 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1085 = subst' s t1 in
               let uu____1086 =
                 FStar_Option.map (subst_univ (Prims.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1085 uu____1086
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1099 = subst' s t1 in
               let uu____1100 =
                 FStar_Option.map (subst_univ (Prims.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1099 uu____1100
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1106 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1106)
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
      | FStar_Syntax_Syntax.NT uu____1121 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1153 =
    FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1153, (Prims.snd s))
let subst_binder' s uu____1175 =
  match uu____1175 with
  | (x,imp) ->
      let uu____1180 =
        let uu___114_1181 = x in
        let uu____1182 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___114_1181.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___114_1181.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1182
        } in
      (uu____1180, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1223 = shift_subst' i s in
               subst_binder' uu____1223 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1257 =
  match uu____1257 with
  | (t,imp) -> let uu____1268 = subst' s t in (uu____1268, imp)
let subst_args' s = FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list* FStar_Range.range Prims.option) ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t -> (FStar_Syntax_Syntax.pat* Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: empty disjunction"
        | FStar_Syntax_Syntax.Pat_constant uu____1343 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
            let uu____1355 = aux n1 p2 in
            (match uu____1355 with
             | (p3,m) ->
                 let ps1 =
                   FStar_List.map
                     (fun p4  ->
                        let uu____1369 = aux n1 p4 in Prims.fst uu____1369)
                     ps in
                 ((let uu___115_1374 = p3 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                     FStar_Syntax_Syntax.ty =
                       (uu___115_1374.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___115_1374.FStar_Syntax_Syntax.p)
                   }), m))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1387 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1412  ->
                      fun uu____1413  ->
                        match (uu____1412, uu____1413) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1460 = aux n2 p2 in
                            (match uu____1460 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1387 with
             | (pats1,n2) ->
                 ((let uu___116_1492 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___116_1492.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___116_1492.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___117_1508 = x in
              let uu____1509 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1508.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1508.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1509
              } in
            ((let uu___118_1514 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___118_1514.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1514.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___119_1525 = x in
              let uu____1526 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1525.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1525.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1526
              } in
            ((let uu___120_1531 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___120_1531.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___120_1531.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___121_1547 = x in
              let uu____1548 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___121_1547.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___121_1547.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1548
              } in
            let t01 = subst' s1 t0 in
            ((let uu___122_1556 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___122_1556.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___122_1556.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None |Some (FStar_Util.Inr _) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1590 =
        let uu____1593 =
          let uu___123_1594 = l in
          let uu____1595 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___123_1594.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1595;
            FStar_Syntax_Syntax.cflags =
              (uu___123_1594.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1598  ->
                 let uu____1599 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1599)
          } in
        FStar_Util.Inl uu____1593 in
      Some uu____1590
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
        let uu____1622 = mk_range t.FStar_Syntax_Syntax.pos s in
        (FStar_Syntax_Syntax.mk t') None uu____1622 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1633 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_fvar _
         |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uvar _ ->
          tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
          subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (Prims.fst s)) us in
          let uu____1675 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1675 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1696 =
            let uu____1697 =
              let uu____1707 = subst' s t0 in
              let uu____1710 = (subst_args' s) args in
              (uu____1707, uu____1710) in
            FStar_Syntax_Syntax.Tm_app uu____1697 in
          mk1 uu____1696
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inl t1,lopt) ->
          let uu____1744 =
            let uu____1745 =
              let uu____1758 = subst' s t0 in
              let uu____1761 =
                let uu____1768 = subst' s t1 in FStar_Util.Inl uu____1768 in
              (uu____1758, uu____1761, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1745 in
          mk1 uu____1744
      | FStar_Syntax_Syntax.Tm_ascribed (t0,FStar_Util.Inr c,lopt) ->
          let uu____1805 =
            let uu____1806 =
              let uu____1819 = subst' s t0 in
              let uu____1822 =
                let uu____1829 = subst_comp' s c in FStar_Util.Inr uu____1829 in
              (uu____1819, uu____1822, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1806 in
          mk1 uu____1805
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1882 =
            let uu____1883 =
              let uu____1898 = subst_binders' s bs in
              let uu____1902 = subst' s' body in
              let uu____1905 = push_subst_lcomp s' lopt in
              (uu____1898, uu____1902, uu____1905) in
            FStar_Syntax_Syntax.Tm_abs uu____1883 in
          mk1 uu____1882
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1942 =
            let uu____1943 =
              let uu____1951 = subst_binders' s bs in
              let uu____1955 =
                let uu____1958 = shift_subst' n1 s in
                subst_comp' uu____1958 comp in
              (uu____1951, uu____1955) in
            FStar_Syntax_Syntax.Tm_arrow uu____1943 in
          mk1 uu____1942
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___124_1979 = x in
            let uu____1980 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___124_1979.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___124_1979.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1980
            } in
          let phi1 =
            let uu____1986 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____1986 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2069  ->
                    match uu____2069 with
                    | (pat,wopt,branch) ->
                        let uu____2105 = subst_pat' s pat in
                        (match uu____2105 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2140 = subst' s1 w in
                                   Some uu____2140 in
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
                      let uu____2200 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2200
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___125_2210 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___125_2210.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___125_2210.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___126_2212 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___127_2213 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___127_2213.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___127_2213.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___126_2212.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___126_2212.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___128_2228 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_2228.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_2228.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2247 =
            let uu____2248 =
              let uu____2253 = subst' s t0 in
              let uu____2256 =
                let uu____2257 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2257 in
              (uu____2253, uu____2256) in
            FStar_Syntax_Syntax.Tm_meta uu____2248 in
          mk1 uu____2247
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2299 =
            let uu____2300 =
              let uu____2305 = subst' s t0 in
              let uu____2308 =
                let uu____2309 =
                  let uu____2314 = subst' s t1 in (m, uu____2314) in
                FStar_Syntax_Syntax.Meta_monadic uu____2309 in
              (uu____2305, uu____2308) in
            FStar_Syntax_Syntax.Tm_meta uu____2300 in
          mk1 uu____2299
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2333 =
            let uu____2334 =
              let uu____2339 = subst' s t0 in
              let uu____2342 =
                let uu____2343 =
                  let uu____2349 = subst' s t1 in (m1, m2, uu____2349) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2343 in
              (uu____2339, uu____2342) in
            FStar_Syntax_Syntax.Tm_meta uu____2334 in
          mk1 uu____2333
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2362 =
            let uu____2363 = let uu____2368 = subst' s t1 in (uu____2368, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2363 in
          mk1 uu____2362
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2431 = push_subst s t2 in compress uu____2431 in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2438 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2442 -> compress t'
         | uu____2463 -> t')
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
             (let uu___129_2487 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___129_2487.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2515 =
    FStar_List.fold_right
      (fun uu____2524  ->
         fun uu____2525  ->
           match (uu____2524, uu____2525) with
           | ((x,uu____2540),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2515 Prims.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___130_2620 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2621 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___130_2620.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___130_2620.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2621
          } in
        let o1 =
          let uu____2626 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2626 in
        let uu____2628 = aux bs' o1 in
        (match uu____2628 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2660 = open_binders' bs in Prims.fst uu____2660
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2680 = open_binders' bs in
      match uu____2680 with
      | (bs',opening) ->
          let uu____2700 = subst opening t in (bs', uu____2700, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2713 = open_term' bs t in
      match uu____2713 with | (b,t1,uu____2721) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2730 = open_binders' bs in
      match uu____2730 with
      | (bs',opening) ->
          let uu____2749 = subst_comp opening t in (bs', uu____2749)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_disj sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2786 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2792 -> p1
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___131_2805 = p1 in
          let uu____2808 =
            let uu____2809 =
              let uu____2817 =
                FStar_All.pipe_right pats
                  (FStar_List.map
                     (fun uu____2841  ->
                        match uu____2841 with
                        | (p2,b) ->
                            let uu____2856 = aux_disj sub1 renaming p2 in
                            (uu____2856, b))) in
              (fv, uu____2817) in
            FStar_Syntax_Syntax.Pat_cons uu____2809 in
          {
            FStar_Syntax_Syntax.v = uu____2808;
            FStar_Syntax_Syntax.ty = (uu___131_2805.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___131_2805.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___108_2871  ->
                 match uu___108_2871 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2877 -> None) in
          let y =
            match yopt with
            | None  ->
                let uu___132_2881 = FStar_Syntax_Syntax.freshen_bv x in
                let uu____2882 = subst sub1 x.FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___132_2881.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___132_2881.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____2882
                }
            | Some y -> y in
          let uu___133_2886 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___133_2886.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___133_2886.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___134_2891 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2892 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_2891.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_2891.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2892
            } in
          let uu___135_2895 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___135_2895.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___135_2895.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___136_2905 = x in
            let uu____2906 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_2905.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_2905.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2906
            } in
          let t01 = subst sub1 t0 in
          let uu___137_2910 = p1 in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
            FStar_Syntax_Syntax.ty = (uu___137_2910.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___137_2910.FStar_Syntax_Syntax.p)
          } in
    let rec aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____2964 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____2980 = aux sub1 renaming p2 in
          (match uu____2980 with
           | (p3,sub2,renaming1) ->
               let ps1 = FStar_List.map (aux_disj sub2 renaming1) ps in
               ((let uu___138_3028 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___138_3028.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___138_3028.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3045 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3091  ->
                    fun uu____3092  ->
                      match (uu____3091, uu____3092) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____3180 = aux sub2 renaming1 p2 in
                          (match uu____3180 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3045 with
           | (pats1,sub2,renaming1) ->
               ((let uu___139_3281 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___139_3281.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___139_3281.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___140_3295 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3296 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3295.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_3295.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3296
            } in
          let sub2 =
            let uu____3301 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3301 in
          ((let uu___141_3309 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___141_3309.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_3309.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___142_3316 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3317 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_3316.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_3316.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3317
            } in
          let sub2 =
            let uu____3322 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3322 in
          ((let uu___143_3330 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___143_3330.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___143_3330.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___144_3342 = x in
            let uu____3343 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___144_3342.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_3342.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3343
            } in
          let t01 = subst sub1 t0 in
          ((let uu___145_3353 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___145_3353.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___145_3353.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3356 = aux [] [] p in
    match uu____3356 with | (p1,sub1,uu____3372) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3390  ->
    match uu____3390 with
    | (p,wopt,e) ->
        let uu____3408 = open_pat p in
        (match uu____3408 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3423 = subst opening w in Some uu____3423 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3432 = closing_subst bs in subst uu____3432 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3440 = closing_subst bs in subst_comp uu____3440 c
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
            let uu___146_3473 = x in
            let uu____3474 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_3473.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___146_3473.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3474
            } in
          let s' =
            let uu____3479 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3479 in
          let uu____3481 = aux s' tl1 in (x1, imp) :: uu____3481 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___147_3495 = lc in
      let uu____3496 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___147_3495.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3496;
        FStar_Syntax_Syntax.cflags =
          (uu___147_3495.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3499  ->
             let uu____3500 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3500)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3543 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3556 = aux sub1 p2 in
          (match uu____3556 with
           | (p3,sub2) ->
               let ps1 =
                 FStar_List.map
                   (fun p4  ->
                      let uu____3586 = aux sub2 p4 in Prims.fst uu____3586)
                   ps in
               ((let uu___148_3598 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___148_3598.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___148_3598.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3615 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3649  ->
                    fun uu____3650  ->
                      match (uu____3649, uu____3650) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3715 = aux sub2 p2 in
                          (match uu____3715 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3615 with
           | (pats1,sub2) ->
               ((let uu___149_3781 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___149_3781.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___149_3781.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___150_3795 = x in
            let uu____3796 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___150_3795.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___150_3795.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3796
            } in
          let sub2 =
            let uu____3801 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3801 in
          ((let uu___151_3806 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___151_3806.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___151_3806.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___152_3811 = x in
            let uu____3812 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___152_3811.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___152_3811.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3812
            } in
          let sub2 =
            let uu____3817 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3817 in
          ((let uu___153_3822 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___153_3822.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___153_3822.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___154_3832 = x in
            let uu____3833 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___154_3832.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___154_3832.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3833
            } in
          let t01 = subst sub1 t0 in
          ((let uu___155_3840 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___155_3840.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___155_3840.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3845  ->
    match uu____3845 with
    | (p,wopt,e) ->
        let uu____3863 = close_pat p in
        (match uu____3863 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3887 = subst closing w in Some uu____3887 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3903 =
      let uu____3908 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3908 FStar_List.unzip in
    match uu____3903 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3949 = univ_var_opening us in
      match uu____3949 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3974 = univ_var_opening us in
      match uu____3974 with
      | (s,us') -> let uu____3987 = subst_comp s c in (us', uu____3987)
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
      let uu____4030 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4030
      then (lbs, t)
      else
        (let uu____4036 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4048  ->
                  match uu____4048 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____4067 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____4067 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___156_4070 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___156_4070.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___156_4070.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___156_4070.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___156_4070.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____4036 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4088 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4100  ->
                                match uu____4100 with
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
                       match uu____4088 with
                       | (uu____4123,us,u_let_rec_opening) ->
                           let uu___157_4130 = lb in
                           let uu____4131 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___157_4130.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___157_4130.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___157_4130.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4131
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____4147 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4147
      then (lbs, t)
      else
        (let uu____4153 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4161  ->
                  match uu____4161 with
                  | (i,out) ->
                      let uu____4172 =
                        let uu____4174 =
                          let uu____4175 =
                            let uu____4178 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____4178, i) in
                          FStar_Syntax_Syntax.NM uu____4175 in
                        uu____4174 :: out in
                      ((i + (Prims.parse_int "1")), uu____4172)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____4153 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4193 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4201  ->
                                match uu____4201 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____4193 with
                       | (uu____4214,u_let_rec_closing) ->
                           let uu___158_4218 = lb in
                           let uu____4219 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___158_4218.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___158_4218.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___158_4218.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___158_4218.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4219
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____4229  ->
      match uu____4229 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____4247  ->
                   match uu____4247 with
                   | (x,uu____4251) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4262  ->
      match uu____4262 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____4280 = subst s t in (us', uu____4280)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4295  ->
              match uu____4295 with
              | (x,uu____4299) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))