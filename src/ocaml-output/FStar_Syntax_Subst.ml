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
let map_some_curry f x uu___98_101 =
  match uu___98_101 with | None  -> x | Some (a,b) -> f a b
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
        (fun uu___99_552  ->
           match uu___99_552 with
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
        (fun uu___100_569  ->
           match uu___100_569 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____573 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___105_574 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___105_574.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___105_574.FStar_Syntax_Syntax.sort)
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
        (fun uu___101_593  ->
           match uu___101_593 with
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
        (fun uu___102_607  ->
           match uu___102_607 with
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
              let uu___106_675 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___106_675.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___106_675.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___107_691 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___107_691.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___107_691.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___108_693 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___108_693.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___108_693.FStar_Syntax_Syntax.vars)
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
           (fun uu___103_972  ->
              match uu___103_972 with
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
          let uu___109_1002 = t in
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
        let uu___110_1181 = x in
        let uu____1182 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___110_1181.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___110_1181.FStar_Syntax_Syntax.index);
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
                 ((let uu___111_1374 = p3 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                     FStar_Syntax_Syntax.ty =
                       (uu___111_1374.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___111_1374.FStar_Syntax_Syntax.p)
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
                 ((let uu___112_1492 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___112_1492.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___112_1492.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___113_1508 = x in
              let uu____1509 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___113_1508.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___113_1508.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1509
              } in
            ((let uu___114_1514 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___114_1514.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___114_1514.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___115_1525 = x in
              let uu____1526 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1525.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1525.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1526
              } in
            ((let uu___116_1531 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1531.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1531.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___117_1547 = x in
              let uu____1548 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1547.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1547.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1548
              } in
            let t01 = subst' s1 t0 in
            ((let uu___118_1556 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___118_1556.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1556.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None |Some (FStar_Util.Inr _) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1590 =
        let uu____1593 =
          let uu___119_1594 = l in
          let uu____1595 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___119_1594.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1595;
            FStar_Syntax_Syntax.cflags =
              (uu___119_1594.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (FStar_Util.Inl
                 (fun uu____1604  ->
                    let uu____1605 = FStar_Syntax_Syntax.get_comp_of_lcomp l in
                    subst_comp' s uu____1605))
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
        let uu____1628 = mk_range t.FStar_Syntax_Syntax.pos s in
        (FStar_Syntax_Syntax.mk t') None uu____1628 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1639 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_fvar _
         |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uvar _ ->
          tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
          subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (Prims.fst s)) us in
          let uu____1681 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1681 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1702 =
            let uu____1703 =
              let uu____1713 = subst' s t0 in
              let uu____1716 = (subst_args' s) args in
              (uu____1713, uu____1716) in
            FStar_Syntax_Syntax.Tm_app uu____1703 in
          mk1 uu____1702
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1788 = subst' s t1 in FStar_Util.Inl uu____1788
            | FStar_Util.Inr c ->
                let uu____1802 = subst_comp' s c in FStar_Util.Inr uu____1802 in
          let uu____1809 =
            let uu____1810 =
              let uu____1828 = subst' s t0 in
              let uu____1831 =
                let uu____1843 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1843) in
              (uu____1828, uu____1831, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1810 in
          mk1 uu____1809
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1911 =
            let uu____1912 =
              let uu____1927 = subst_binders' s bs in
              let uu____1931 = subst' s' body in
              let uu____1934 = push_subst_lcomp s' lopt in
              (uu____1927, uu____1931, uu____1934) in
            FStar_Syntax_Syntax.Tm_abs uu____1912 in
          mk1 uu____1911
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1971 =
            let uu____1972 =
              let uu____1980 = subst_binders' s bs in
              let uu____1984 =
                let uu____1987 = shift_subst' n1 s in
                subst_comp' uu____1987 comp in
              (uu____1980, uu____1984) in
            FStar_Syntax_Syntax.Tm_arrow uu____1972 in
          mk1 uu____1971
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___120_2008 = x in
            let uu____2009 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___120_2008.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___120_2008.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2009
            } in
          let phi1 =
            let uu____2015 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2015 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2098  ->
                    match uu____2098 with
                    | (pat,wopt,branch) ->
                        let uu____2134 = subst_pat' s pat in
                        (match uu____2134 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2169 = subst' s1 w in
                                   Some uu____2169 in
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
                      let uu____2229 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2229
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___121_2239 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___121_2239.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___121_2239.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___122_2241 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___123_2242 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___123_2242.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___123_2242.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___122_2241.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___122_2241.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___124_2257 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___124_2257.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___124_2257.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2276 =
            let uu____2277 =
              let uu____2282 = subst' s t0 in
              let uu____2285 =
                let uu____2286 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2286 in
              (uu____2282, uu____2285) in
            FStar_Syntax_Syntax.Tm_meta uu____2277 in
          mk1 uu____2276
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2328 =
            let uu____2329 =
              let uu____2334 = subst' s t0 in
              let uu____2337 =
                let uu____2338 =
                  let uu____2343 = subst' s t1 in (m, uu____2343) in
                FStar_Syntax_Syntax.Meta_monadic uu____2338 in
              (uu____2334, uu____2337) in
            FStar_Syntax_Syntax.Tm_meta uu____2329 in
          mk1 uu____2328
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2362 =
            let uu____2363 =
              let uu____2368 = subst' s t0 in
              let uu____2371 =
                let uu____2372 =
                  let uu____2378 = subst' s t1 in (m1, m2, uu____2378) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2372 in
              (uu____2368, uu____2371) in
            FStar_Syntax_Syntax.Tm_meta uu____2363 in
          mk1 uu____2362
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2391 =
            let uu____2392 = let uu____2397 = subst' s t1 in (uu____2397, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2392 in
          mk1 uu____2391
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2460 = push_subst s t2 in compress uu____2460 in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2467 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2471 -> compress t'
         | uu____2492 -> t')
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
             (let uu___125_2516 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___125_2516.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2544 =
    FStar_List.fold_right
      (fun uu____2553  ->
         fun uu____2554  ->
           match (uu____2553, uu____2554) with
           | ((x,uu____2569),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2544 Prims.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___126_2649 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2650 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___126_2649.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___126_2649.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2650
          } in
        let o1 =
          let uu____2655 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2655 in
        let uu____2657 = aux bs' o1 in
        (match uu____2657 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2689 = open_binders' bs in Prims.fst uu____2689
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2709 = open_binders' bs in
      match uu____2709 with
      | (bs',opening) ->
          let uu____2729 = subst opening t in (bs', uu____2729, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2742 = open_term' bs t in
      match uu____2742 with | (b,t1,uu____2750) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2759 = open_binders' bs in
      match uu____2759 with
      | (bs',opening) ->
          let uu____2778 = subst_comp opening t in (bs', uu____2778)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec aux_disj sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj uu____2815 -> failwith "impossible"
      | FStar_Syntax_Syntax.Pat_constant uu____2821 -> p1
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu___127_2834 = p1 in
          let uu____2837 =
            let uu____2838 =
              let uu____2846 =
                FStar_All.pipe_right pats
                  (FStar_List.map
                     (fun uu____2870  ->
                        match uu____2870 with
                        | (p2,b) ->
                            let uu____2885 = aux_disj sub1 renaming p2 in
                            (uu____2885, b))) in
              (fv, uu____2846) in
            FStar_Syntax_Syntax.Pat_cons uu____2838 in
          {
            FStar_Syntax_Syntax.v = uu____2837;
            FStar_Syntax_Syntax.ty = (uu___127_2834.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___127_2834.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_var x ->
          let yopt =
            FStar_Util.find_map renaming
              (fun uu___104_2900  ->
                 match uu___104_2900 with
                 | (x',y) when
                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       (x'.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                     -> Some y
                 | uu____2906 -> None) in
          let y =
            match yopt with
            | None  ->
                let uu___128_2910 = FStar_Syntax_Syntax.freshen_bv x in
                let uu____2911 = subst sub1 x.FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___128_2910.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___128_2910.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____2911
                }
            | Some y -> y in
          let uu___129_2915 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var y);
            FStar_Syntax_Syntax.ty = (uu___129_2915.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___129_2915.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___130_2920 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2921 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_2920.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_2920.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2921
            } in
          let uu___131_2924 = p1 in
          {
            FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
            FStar_Syntax_Syntax.ty = (uu___131_2924.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___131_2924.FStar_Syntax_Syntax.p)
          }
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___132_2934 = x in
            let uu____2935 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_2934.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_2934.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2935
            } in
          let t01 = subst sub1 t0 in
          let uu___133_2939 = p1 in
          {
            FStar_Syntax_Syntax.v =
              (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
            FStar_Syntax_Syntax.ty = (uu___133_2939.FStar_Syntax_Syntax.ty);
            FStar_Syntax_Syntax.p = (uu___133_2939.FStar_Syntax_Syntax.p)
          } in
    let rec aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj [] ->
          failwith "Impossible: empty disjunction"
      | FStar_Syntax_Syntax.Pat_constant uu____2993 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3009 = aux sub1 renaming p2 in
          (match uu____3009 with
           | (p3,sub2,renaming1) ->
               let ps1 = FStar_List.map (aux_disj sub2 renaming1) ps in
               ((let uu___134_3057 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___134_3057.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___134_3057.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3074 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3120  ->
                    fun uu____3121  ->
                      match (uu____3120, uu____3121) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____3209 = aux sub2 renaming1 p2 in
                          (match uu____3209 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3074 with
           | (pats1,sub2,renaming1) ->
               ((let uu___135_3310 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___135_3310.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___135_3310.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___136_3324 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3325 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_3324.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_3324.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3325
            } in
          let sub2 =
            let uu____3330 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3330 in
          ((let uu___137_3338 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___137_3338.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___137_3338.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___138_3345 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3346 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_3345.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_3345.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3346
            } in
          let sub2 =
            let uu____3351 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3351 in
          ((let uu___139_3359 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___139_3359.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_3359.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___140_3371 = x in
            let uu____3372 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3371.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_3371.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3372
            } in
          let t01 = subst sub1 t0 in
          ((let uu___141_3382 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___141_3382.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_3382.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3385 = aux [] [] p in
    match uu____3385 with | (p1,sub1,uu____3401) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3419  ->
    match uu____3419 with
    | (p,wopt,e) ->
        let uu____3437 = open_pat p in
        (match uu____3437 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3452 = subst opening w in Some uu____3452 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3461 = closing_subst bs in subst uu____3461 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3469 = closing_subst bs in subst_comp uu____3469 c
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
            let uu___142_3502 = x in
            let uu____3503 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_3502.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_3502.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3503
            } in
          let s' =
            let uu____3508 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3508 in
          let uu____3510 = aux s' tl1 in (x1, imp) :: uu____3510 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___143_3524 = lc in
      let uu____3525 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___143_3524.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3525;
        FStar_Syntax_Syntax.cflags =
          (uu___143_3524.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (FStar_Util.Inl
             (fun uu____3532  ->
                let uu____3533 = FStar_Syntax_Syntax.get_comp_of_lcomp lc in
                subst_comp s uu____3533))
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
      | FStar_Syntax_Syntax.Pat_constant uu____3576 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_disj (p2::ps) ->
          let uu____3589 = aux sub1 p2 in
          (match uu____3589 with
           | (p3,sub2) ->
               let ps1 =
                 FStar_List.map
                   (fun p4  ->
                      let uu____3619 = aux sub2 p4 in Prims.fst uu____3619)
                   ps in
               ((let uu___144_3631 = p3 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_disj (p3 :: ps1));
                   FStar_Syntax_Syntax.ty =
                     (uu___144_3631.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___144_3631.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3648 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3682  ->
                    fun uu____3683  ->
                      match (uu____3682, uu____3683) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3748 = aux sub2 p2 in
                          (match uu____3748 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3648 with
           | (pats1,sub2) ->
               ((let uu___145_3814 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___145_3814.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___145_3814.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___146_3828 = x in
            let uu____3829 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_3828.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___146_3828.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3829
            } in
          let sub2 =
            let uu____3834 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3834 in
          ((let uu___147_3839 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___147_3839.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___147_3839.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___148_3844 = x in
            let uu____3845 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_3844.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_3844.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3845
            } in
          let sub2 =
            let uu____3850 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3850 in
          ((let uu___149_3855 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___149_3855.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___149_3855.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___150_3865 = x in
            let uu____3866 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___150_3865.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___150_3865.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3866
            } in
          let t01 = subst sub1 t0 in
          ((let uu___151_3873 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___151_3873.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___151_3873.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3878  ->
    match uu____3878 with
    | (p,wopt,e) ->
        let uu____3896 = close_pat p in
        (match uu____3896 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3920 = subst closing w in Some uu____3920 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3936 =
      let uu____3941 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3941 FStar_List.unzip in
    match uu____3936 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3982 = univ_var_opening us in
      match uu____3982 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____4007 = univ_var_opening us in
      match uu____4007 with
      | (s,us') -> let uu____4020 = subst_comp s c in (us', uu____4020)
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
      let uu____4063 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4063
      then (lbs, t)
      else
        (let uu____4069 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4081  ->
                  match uu____4081 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____4100 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____4100 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___152_4103 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___152_4103.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___152_4103.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___152_4103.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___152_4103.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____4069 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4121 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4133  ->
                                match uu____4133 with
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
                       match uu____4121 with
                       | (uu____4156,us,u_let_rec_opening) ->
                           let uu___153_4163 = lb in
                           let uu____4164 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___153_4163.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___153_4163.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___153_4163.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4164
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____4180 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____4180
      then (lbs, t)
      else
        (let uu____4186 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____4194  ->
                  match uu____4194 with
                  | (i,out) ->
                      let uu____4205 =
                        let uu____4207 =
                          let uu____4208 =
                            let uu____4211 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____4211, i) in
                          FStar_Syntax_Syntax.NM uu____4208 in
                        uu____4207 :: out in
                      ((i + (Prims.parse_int "1")), uu____4205)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____4186 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____4226 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____4234  ->
                                match uu____4234 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____4226 with
                       | (uu____4247,u_let_rec_closing) ->
                           let uu___154_4251 = lb in
                           let uu____4252 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___154_4251.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___154_4251.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___154_4251.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___154_4251.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4252
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____4262  ->
      match uu____4262 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____4280  ->
                   match uu____4280 with
                   | (x,uu____4284) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4295  ->
      match uu____4295 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____4313 = subst s t in (us', uu____4313)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4328  ->
              match uu____4328 with
              | (x,uu____4332) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))