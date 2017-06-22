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
      let uu____63 = f s0 in
      (match uu____63 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
let map_some_curry f x uu___99_103 =
  match uu___99_103 with | None  -> x | Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____164 = apply_until_some f s in
  FStar_All.pipe_right uu____164 (map_some_curry g t)
let compose_subst s1 s2 =
  let s = FStar_List.append (fst s1) (fst s2) in
  let ropt =
    match snd s2 with | Some uu____219 -> snd s2 | uu____222 -> snd s1 in
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
      | uu____318 ->
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
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____349) ->
        let uu____362 = FStar_Unionfind.find uv in
        (match uu____362 with
         | FStar_Syntax_Syntax.Fixed t' -> force_uvar' t'
         | uu____376 -> t)
    | uu____380 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____393 = FStar_Util.physical_equality t t' in
    if uu____393
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
        let uu____452 = FStar_ST.read m in
        (match uu____452 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____488 = c () in force_delayed_thunk uu____488 in
                  (FStar_ST.write m (Some t'); t')
              | uu____499 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____531 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____538 = FStar_Unionfind.find u' in
        (match uu____538 with | Some u1 -> compress_univ u1 | uu____542 -> u)
    | uu____544 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___100_554  ->
           match uu___100_554 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____558 =
                 let uu____559 =
                   let uu____560 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____560 in
                 FStar_Syntax_Syntax.bv_to_name uu____559 in
               Some uu____558
           | uu____561 -> None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___101_571  ->
           match uu___101_571 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____575 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___105_576 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___105_576.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___105_576.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____575
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____585 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___102_595  ->
           match uu___102_595 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____599 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_609  ->
           match uu___103_609 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____613 -> None)
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
      | FStar_Syntax_Syntax.U_unif uu____629 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____633 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____633
      | FStar_Syntax_Syntax.U_max us ->
          let uu____636 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____636
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____669 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____669
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____671 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____671
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___106_679 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___106_679.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___106_679.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___107_695 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___107_695.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___107_695.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___108_697 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___108_697.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___108_697.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____724 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____724
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
      | uu____810 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____818 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____821 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____824 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____905,uu____906) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____962 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____963 =
                 let uu____966 =
                   let uu____967 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____967 in
                 FStar_Syntax_Syntax.mk uu____966 in
               uu____963 None uu____962
           | uu____979 ->
               let uu____980 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____980)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___104_994  ->
              match uu___104_994 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____998 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____998
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
      | uu____1018 ->
          let uu___109_1024 = t in
          let uu____1025 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1029 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1032 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1035 =
            FStar_List.map
              (fun uu____1049  ->
                 match uu____1049 with
                 | (t1,imp) ->
                     let uu____1064 = subst' s t1 in (uu____1064, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1069 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1025;
            FStar_Syntax_Syntax.effect_name = uu____1029;
            FStar_Syntax_Syntax.result_typ = uu____1032;
            FStar_Syntax_Syntax.effect_args = uu____1035;
            FStar_Syntax_Syntax.flags = uu____1069
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
      | uu____1091 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1107 = subst' s t1 in
               let uu____1108 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1107 uu____1108
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1121 = subst' s t1 in
               let uu____1122 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1121 uu____1122
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1128 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1128)
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
      | FStar_Syntax_Syntax.NT uu____1143 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1175 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1175, (snd s))
let subst_binder' s uu____1197 =
  match uu____1197 with
  | (x,imp) ->
      let uu____1202 =
        let uu___110_1203 = x in
        let uu____1204 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___110_1203.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___110_1203.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1204
        } in
      (uu____1202, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1245 = shift_subst' i s in
               subst_binder' uu____1245 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1279 =
  match uu____1279 with
  | (t,imp) -> let uu____1290 = subst' s t in (uu____1290, imp)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1361 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1376 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1401  ->
                      fun uu____1402  ->
                        match (uu____1401, uu____1402) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1449 = aux n2 p2 in
                            (match uu____1449 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1376 with
             | (pats1,n2) ->
                 ((let uu___111_1481 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___111_1481.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___111_1481.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___112_1497 = x in
              let uu____1498 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___112_1497.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___112_1497.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1498
              } in
            ((let uu___113_1503 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___113_1503.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___113_1503.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___114_1514 = x in
              let uu____1515 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___114_1514.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___114_1514.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1515
              } in
            ((let uu___115_1520 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___115_1520.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___115_1520.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_1536 = x in
              let uu____1537 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_1536.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_1536.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1537
              } in
            let t01 = subst' s1 t0 in
            ((let uu___117_1545 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___117_1545.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___117_1545.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None  -> lopt
  | Some (FStar_Util.Inr uu____1573) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1579 =
        let uu____1582 =
          let uu___118_1583 = l in
          let uu____1584 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___118_1583.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1584;
            FStar_Syntax_Syntax.cflags =
              (uu___118_1583.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1587  ->
                 let uu____1588 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1588)
          } in
        FStar_Util.Inl uu____1582 in
      Some uu____1579
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
        let uu____1611 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1611 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1618 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1641 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1644 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1649 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1660 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1661 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1662 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1674 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1674 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1695 =
            let uu____1696 =
              let uu____1706 = subst' s t0 in
              let uu____1709 = subst_args' s args in (uu____1706, uu____1709) in
            FStar_Syntax_Syntax.Tm_app uu____1696 in
          mk1 uu____1695
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1781 = subst' s t1 in FStar_Util.Inl uu____1781
            | FStar_Util.Inr c ->
                let uu____1795 = subst_comp' s c in FStar_Util.Inr uu____1795 in
          let uu____1802 =
            let uu____1803 =
              let uu____1821 = subst' s t0 in
              let uu____1824 =
                let uu____1836 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1836) in
              (uu____1821, uu____1824, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1803 in
          mk1 uu____1802
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1904 =
            let uu____1905 =
              let uu____1920 = subst_binders' s bs in
              let uu____1924 = subst' s' body in
              let uu____1927 = push_subst_lcomp s' lopt in
              (uu____1920, uu____1924, uu____1927) in
            FStar_Syntax_Syntax.Tm_abs uu____1905 in
          mk1 uu____1904
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1964 =
            let uu____1965 =
              let uu____1973 = subst_binders' s bs in
              let uu____1977 =
                let uu____1980 = shift_subst' n1 s in
                subst_comp' uu____1980 comp in
              (uu____1973, uu____1977) in
            FStar_Syntax_Syntax.Tm_arrow uu____1965 in
          mk1 uu____1964
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___119_2001 = x in
            let uu____2002 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_2001.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_2001.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2002
            } in
          let phi1 =
            let uu____2008 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2008 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2091  ->
                    match uu____2091 with
                    | (pat,wopt,branch) ->
                        let uu____2127 = subst_pat' s pat in
                        (match uu____2127 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2162 = subst' s1 w in
                                   Some uu____2162 in
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
                      let uu____2222 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2222
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___120_2232 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___120_2232.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___120_2232.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___121_2234 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___122_2235 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___122_2235.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___122_2235.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___121_2234.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___121_2234.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___123_2250 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___123_2250.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___123_2250.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2269 =
            let uu____2270 =
              let uu____2275 = subst' s t0 in
              let uu____2278 =
                let uu____2279 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2279 in
              (uu____2275, uu____2278) in
            FStar_Syntax_Syntax.Tm_meta uu____2270 in
          mk1 uu____2269
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2321 =
            let uu____2322 =
              let uu____2327 = subst' s t0 in
              let uu____2330 =
                let uu____2331 =
                  let uu____2336 = subst' s t1 in (m, uu____2336) in
                FStar_Syntax_Syntax.Meta_monadic uu____2331 in
              (uu____2327, uu____2330) in
            FStar_Syntax_Syntax.Tm_meta uu____2322 in
          mk1 uu____2321
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2355 =
            let uu____2356 =
              let uu____2361 = subst' s t0 in
              let uu____2364 =
                let uu____2365 =
                  let uu____2371 = subst' s t1 in (m1, m2, uu____2371) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2365 in
              (uu____2361, uu____2364) in
            FStar_Syntax_Syntax.Tm_meta uu____2356 in
          mk1 uu____2355
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2384 =
            let uu____2385 = let uu____2390 = subst' s t1 in (uu____2390, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2385 in
          mk1 uu____2384
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2453 = push_subst s t2 in compress uu____2453 in
        (FStar_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2460 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2464 -> compress t'
         | uu____2485 -> t')
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
             (let uu___124_2509 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___124_2509.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2537 =
    FStar_List.fold_right
      (fun uu____2546  ->
         fun uu____2547  ->
           match (uu____2546, uu____2547) with
           | ((x,uu____2562),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2537 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___125_2642 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2643 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___125_2642.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___125_2642.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2643
          } in
        let o1 =
          let uu____2648 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2648 in
        let uu____2650 = aux bs' o1 in
        (match uu____2650 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2682 = open_binders' bs in fst uu____2682
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2702 = open_binders' bs in
      match uu____2702 with
      | (bs',opening) ->
          let uu____2722 = subst opening t in (bs', uu____2722, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2735 = open_term' bs t in
      match uu____2735 with | (b,t1,uu____2743) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2752 = open_binders' bs in
      match uu____2752 with
      | (bs',opening) ->
          let uu____2771 = subst_comp opening t in (bs', uu____2771)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2822 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2841 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2887  ->
                    fun uu____2888  ->
                      match (uu____2887, uu____2888) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2976 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2976 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2841 with
           | (pats1,sub2,renaming1) ->
               ((let uu___126_3077 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___126_3077.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___126_3077.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___127_3091 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3092 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_3091.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_3091.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3092
            } in
          let sub2 =
            let uu____3097 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3097 in
          ((let uu___128_3105 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___128_3105.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___128_3105.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___129_3112 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3113 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_3112.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_3112.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3113
            } in
          let sub2 =
            let uu____3118 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3118 in
          ((let uu___130_3126 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___130_3126.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___130_3126.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___131_3138 = x in
            let uu____3139 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_3138.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_3138.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3139
            } in
          let t01 = subst sub1 t0 in
          ((let uu___132_3149 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___132_3149.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___132_3149.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3152 = open_pat_aux [] [] p in
    match uu____3152 with | (p1,sub1,uu____3168) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3186  ->
    match uu____3186 with
    | (p,wopt,e) ->
        let uu____3204 = open_pat p in
        (match uu____3204 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3219 = subst opening w in Some uu____3219 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3228 = closing_subst bs in subst uu____3228 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3236 = closing_subst bs in subst_comp uu____3236 c
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
            let uu___133_3269 = x in
            let uu____3270 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_3269.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_3269.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3270
            } in
          let s' =
            let uu____3275 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3275 in
          let uu____3277 = aux s' tl1 in (x1, imp) :: uu____3277 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___134_3291 = lc in
      let uu____3292 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___134_3291.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3292;
        FStar_Syntax_Syntax.cflags =
          (uu___134_3291.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3295  ->
             let uu____3296 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3296)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3332 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3348 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3382  ->
                    fun uu____3383  ->
                      match (uu____3382, uu____3383) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3448 = aux sub2 p2 in
                          (match uu____3448 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3348 with
           | (pats1,sub2) ->
               ((let uu___135_3514 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___135_3514.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___135_3514.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___136_3528 = x in
            let uu____3529 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_3528.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_3528.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3529
            } in
          let sub2 =
            let uu____3534 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3534 in
          ((let uu___137_3539 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___137_3539.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___137_3539.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___138_3544 = x in
            let uu____3545 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_3544.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_3544.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3545
            } in
          let sub2 =
            let uu____3550 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3550 in
          ((let uu___139_3555 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___139_3555.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_3555.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___140_3565 = x in
            let uu____3566 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_3565.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_3565.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3566
            } in
          let t01 = subst sub1 t0 in
          ((let uu___141_3573 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___141_3573.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_3573.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3578  ->
    match uu____3578 with
    | (p,wopt,e) ->
        let uu____3596 = close_pat p in
        (match uu____3596 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3620 = subst closing w in Some uu____3620 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3636 =
      let uu____3641 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3641 FStar_List.unzip in
    match uu____3636 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3682 = univ_var_opening us in
      match uu____3682 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3707 = univ_var_opening us in
      match uu____3707 with
      | (s,us') -> let uu____3720 = subst_comp s c in (us', uu____3720)
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
      let uu____3763 =
        let uu____3769 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____3769
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____3784  ->
                 match uu____3784 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____3803 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____3803 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___142_3806 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___142_3806.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___142_3806.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___142_3806.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___142_3806.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____3763 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____3824 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____3836  ->
                             match uu____3836 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____3824 with
                    | (uu____3859,us,u_let_rec_opening) ->
                        let uu___143_3866 = lb in
                        let uu____3867 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____3870 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___143_3866.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____3867;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___143_3866.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3870
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3886 =
        let uu____3890 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____3890
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____3900  ->
                 match uu____3900 with
                 | (i,out) ->
                     let uu____3911 =
                       let uu____3913 =
                         let uu____3914 =
                           let uu____3917 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____3917, i) in
                         FStar_Syntax_Syntax.NM uu____3914 in
                       uu____3913 :: out in
                     ((i + (Prims.parse_int "1")), uu____3911)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____3886 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____3932 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____3940  ->
                             match uu____3940 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____3932 with
                    | (uu____3953,u_let_rec_closing) ->
                        let uu___144_3957 = lb in
                        let uu____3958 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____3961 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___144_3957.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___144_3957.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____3958;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___144_3957.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3961
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3971  ->
      match uu____3971 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3989  ->
                   match uu____3989 with
                   | (x,uu____3993) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____4004  ->
      match uu____4004 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____4022 = subst s t in (us', uu____4022)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4037  ->
              match uu____4037 with
              | (x,uu____4041) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))