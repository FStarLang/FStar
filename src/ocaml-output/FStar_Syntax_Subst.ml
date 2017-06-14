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
        let uu____364 = FStar_Syntax_Unionfind.find uv in
        (match uu____364 with | Some t' -> force_uvar' t' | uu____369 -> t)
    | uu____371 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____384 = FStar_Util.physical_equality t t' in
    if uu____384
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
        let uu____443 = FStar_ST.read m in
        (match uu____443 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____479 = c () in force_delayed_thunk uu____479 in
                  (FStar_ST.write m (Some t'); t')
              | uu____490 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____522 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____531 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____531 with | Some u1 -> compress_univ u1 | uu____534 -> u)
    | uu____536 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___103_546  ->
           match uu___103_546 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____550 =
                 let uu____551 =
                   let uu____552 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____552 in
                 FStar_Syntax_Syntax.bv_to_name uu____551 in
               Some uu____550
           | uu____553 -> None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_563  ->
           match uu___104_563 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____567 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___108_568 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___108_568.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___108_568.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____567
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____577 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_587  ->
           match uu___105_587 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____591 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_601  ->
           match uu___106_601 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____605 -> None)
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
      | FStar_Syntax_Syntax.U_unif uu____621 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____627 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____627
      | FStar_Syntax_Syntax.U_max us ->
          let uu____630 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____630
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____663 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____663
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____665 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____665
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___109_670 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.p = (uu___109_670.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___110_672 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___110_672.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___110_672.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___111_674 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___111_674.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___111_674.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____701 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____701
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
      | uu____783 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____791 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____794 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____797 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____880,uu____881) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____937 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____938 =
                 let uu____941 =
                   let uu____942 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____942 in
                 FStar_Syntax_Syntax.mk uu____941 in
               uu____938 None uu____937
           | uu____954 ->
               let uu____955 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____955)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___107_969  ->
              match uu___107_969 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____973 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____973
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
      | uu____993 ->
          let uu___112_999 = t in
          let uu____1000 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1004 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1007 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1010 =
            FStar_List.map
              (fun uu____1024  ->
                 match uu____1024 with
                 | (t1,imp) ->
                     let uu____1039 = subst' s t1 in (uu____1039, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1044 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1000;
            FStar_Syntax_Syntax.effect_name = uu____1004;
            FStar_Syntax_Syntax.result_typ = uu____1007;
            FStar_Syntax_Syntax.effect_args = uu____1010;
            FStar_Syntax_Syntax.flags = uu____1044
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
      | uu____1066 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1082 = subst' s t1 in
               let uu____1083 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1082 uu____1083
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1096 = subst' s t1 in
               let uu____1097 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1096 uu____1097
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1103 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1103)
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
      | FStar_Syntax_Syntax.NT uu____1118 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1150 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1150, (snd s))
let subst_binder' s uu____1172 =
  match uu____1172 with
  | (x,imp) ->
      let uu____1177 =
        let uu___113_1178 = x in
        let uu____1179 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___113_1178.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___113_1178.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1179
        } in
      (uu____1177, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1220 = shift_subst' i s in
               subst_binder' uu____1220 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1254 =
  match uu____1254 with
  | (t,imp) -> let uu____1265 = subst' s t in (uu____1265, imp)
let subst_args' s = FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list* FStar_Range.range option) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat* Prims.int)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1332 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1344 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1367  ->
                      fun uu____1368  ->
                        match (uu____1367, uu____1368) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1410 = aux n2 p2 in
                            (match uu____1410 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1344 with
             | (pats1,n2) ->
                 ((let uu___114_1441 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___114_1441.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___115_1456 = x in
              let uu____1457 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1456.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1456.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1457
              } in
            ((let uu___116_1461 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___116_1461.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___117_1471 = x in
              let uu____1472 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1471.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1471.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1472
              } in
            ((let uu___118_1476 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___118_1476.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___119_1491 = x in
              let uu____1492 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1491.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1491.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1492
              } in
            let t01 = subst' s1 t0 in
            ((let uu___120_1499 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___120_1499.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None  -> lopt
  | Some (FStar_Util.Inr uu____1526) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1532 =
        let uu____1535 =
          let uu___121_1536 = l in
          let uu____1537 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___121_1536.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1537;
            FStar_Syntax_Syntax.cflags =
              (uu___121_1536.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1540  ->
                 let uu____1541 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1541)
          } in
        FStar_Util.Inl uu____1535 in
      Some uu____1532
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
        let uu____1564 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1564 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1571 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1594 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1597 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1602 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1615 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1616 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1617 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1629 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1629 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1650 =
            let uu____1651 =
              let uu____1661 = subst' s t0 in
              let uu____1664 = subst_args' s args in (uu____1661, uu____1664) in
            FStar_Syntax_Syntax.Tm_app uu____1651 in
          mk1 uu____1650
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1736 = subst' s t1 in FStar_Util.Inl uu____1736
            | FStar_Util.Inr c ->
                let uu____1750 = subst_comp' s c in FStar_Util.Inr uu____1750 in
          let uu____1757 =
            let uu____1758 =
              let uu____1776 = subst' s t0 in
              let uu____1779 =
                let uu____1791 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1791) in
              (uu____1776, uu____1779, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1758 in
          mk1 uu____1757
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1859 =
            let uu____1860 =
              let uu____1875 = subst_binders' s bs in
              let uu____1879 = subst' s' body in
              let uu____1882 = push_subst_lcomp s' lopt in
              (uu____1875, uu____1879, uu____1882) in
            FStar_Syntax_Syntax.Tm_abs uu____1860 in
          mk1 uu____1859
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1919 =
            let uu____1920 =
              let uu____1928 = subst_binders' s bs in
              let uu____1932 =
                let uu____1935 = shift_subst' n1 s in
                subst_comp' uu____1935 comp in
              (uu____1928, uu____1932) in
            FStar_Syntax_Syntax.Tm_arrow uu____1920 in
          mk1 uu____1919
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___122_1956 = x in
            let uu____1957 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_1956.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1956.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1957
            } in
          let phi1 =
            let uu____1963 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____1963 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2042  ->
                    match uu____2042 with
                    | (pat,wopt,branch) ->
                        let uu____2075 = subst_pat' s pat in
                        (match uu____2075 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2110 = subst' s1 w in
                                   Some uu____2110 in
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
                      let uu____2170 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2170
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_2180 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2180.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2180.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___124_2182 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___124_2182.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___124_2182.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2201 =
            let uu____2202 =
              let uu____2207 = subst' s t0 in
              let uu____2210 =
                let uu____2211 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2211 in
              (uu____2207, uu____2210) in
            FStar_Syntax_Syntax.Tm_meta uu____2202 in
          mk1 uu____2201
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2253 =
            let uu____2254 =
              let uu____2259 = subst' s t0 in
              let uu____2262 =
                let uu____2263 =
                  let uu____2268 = subst' s t1 in (m, uu____2268) in
                FStar_Syntax_Syntax.Meta_monadic uu____2263 in
              (uu____2259, uu____2262) in
            FStar_Syntax_Syntax.Tm_meta uu____2254 in
          mk1 uu____2253
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2287 =
            let uu____2288 =
              let uu____2293 = subst' s t0 in
              let uu____2296 =
                let uu____2297 =
                  let uu____2303 = subst' s t1 in (m1, m2, uu____2303) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2297 in
              (uu____2293, uu____2296) in
            FStar_Syntax_Syntax.Tm_meta uu____2288 in
          mk1 uu____2287
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2316 =
            let uu____2317 = let uu____2322 = subst' s t1 in (uu____2322, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2317 in
          mk1 uu____2316
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2385 = push_subst s t2 in compress uu____2385 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2392 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2396 -> compress t'
         | uu____2417 -> t')
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
             (let uu___125_2441 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___125_2441.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2469 =
    FStar_List.fold_right
      (fun uu____2478  ->
         fun uu____2479  ->
           match (uu____2478, uu____2479) with
           | ((x,uu____2494),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2469 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___126_2574 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2575 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___126_2574.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___126_2574.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2575
          } in
        let o1 =
          let uu____2580 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2580 in
        let uu____2582 = aux bs' o1 in
        (match uu____2582 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2614 = open_binders' bs in fst uu____2614
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2634 = open_binders' bs in
      match uu____2634 with
      | (bs',opening) ->
          let uu____2654 = subst opening t in (bs', uu____2654, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2667 = open_term' bs t in
      match uu____2667 with | (b,t1,uu____2675) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2684 = open_binders' bs in
      match uu____2684 with
      | (bs',opening) ->
          let uu____2703 = subst_comp opening t in (bs', uu____2703)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2750 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2766 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2807  ->
                    fun uu____2808  ->
                      match (uu____2807, uu____2808) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2885 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2885 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2766 with
           | (pats1,sub2,renaming1) ->
               ((let uu___127_2973 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___127_2973.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___128_2984 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2985 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_2984.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_2984.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2985
            } in
          let sub2 =
            let uu____2990 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2990 in
          ((let uu___129_2997 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___129_2997.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___130_3003 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3004 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_3003.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_3003.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3004
            } in
          let sub2 =
            let uu____3009 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3009 in
          ((let uu___131_3016 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___131_3016.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___132_3027 = x in
            let uu____3028 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_3027.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_3027.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3028
            } in
          let t01 = subst sub1 t0 in
          ((let uu___133_3037 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___133_3037.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3039 = open_pat_aux [] [] p in
    match uu____3039 with | (p1,sub1,uu____3054) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3069  ->
    match uu____3069 with
    | (p,wopt,e) ->
        let uu____3085 = open_pat p in
        (match uu____3085 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3100 = subst opening w in Some uu____3100 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3109 = closing_subst bs in subst uu____3109 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3117 = closing_subst bs in subst_comp uu____3117 c
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
            let uu___134_3150 = x in
            let uu____3151 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_3150.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_3150.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3151
            } in
          let s' =
            let uu____3156 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3156 in
          let uu____3158 = aux s' tl1 in (x1, imp) :: uu____3158 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___135_3172 = lc in
      let uu____3173 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___135_3172.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3173;
        FStar_Syntax_Syntax.cflags =
          (uu___135_3172.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3176  ->
             let uu____3177 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3177)
      }
let close_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t*
      FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3206 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3219 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3248  ->
                    fun uu____3249  ->
                      match (uu____3248, uu____3249) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3303 = aux sub2 p2 in
                          (match uu____3303 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3219 with
           | (pats1,sub2) ->
               ((let uu___136_3356 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___136_3356.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___137_3367 = x in
            let uu____3368 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___137_3367.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___137_3367.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3368
            } in
          let sub2 =
            let uu____3373 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3373 in
          ((let uu___138_3377 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___138_3377.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___139_3381 = x in
            let uu____3382 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3381.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3381.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3382
            } in
          let sub2 =
            let uu____3387 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3387 in
          ((let uu___140_3391 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___140_3391.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___141_3400 = x in
            let uu____3401 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3400.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3400.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3401
            } in
          let t01 = subst sub1 t0 in
          ((let uu___142_3407 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___142_3407.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3411  ->
    match uu____3411 with
    | (p,wopt,e) ->
        let uu____3427 = close_pat p in
        (match uu____3427 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3448 = subst closing w in Some uu____3448 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3463 =
      let uu____3468 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3468 FStar_List.unzip in
    match uu____3463 with | (s,us') -> (s, us')
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
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3520 = univ_var_opening us in
      match uu____3520 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3545 = univ_var_opening us in
      match uu____3545 with
      | (s,us') -> let uu____3558 = subst_comp s c in (us', uu____3558)
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
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3594 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3594
      then (lbs, t)
      else
        (let uu____3600 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3612  ->
                  match uu____3612 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3631 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3631 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___143_3634 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___143_3634.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___143_3634.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___143_3634.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___143_3634.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3600 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3652 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3664  ->
                                match uu____3664 with
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
                       match uu____3652 with
                       | (uu____3687,us,u_let_rec_opening) ->
                           let uu___144_3694 = lb in
                           let uu____3695 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___144_3694.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___144_3694.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___144_3694.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3695
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3711 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3711
      then (lbs, t)
      else
        (let uu____3717 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3725  ->
                  match uu____3725 with
                  | (i,out) ->
                      let uu____3736 =
                        let uu____3738 =
                          let uu____3739 =
                            let uu____3742 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3742, i) in
                          FStar_Syntax_Syntax.NM uu____3739 in
                        uu____3738 :: out in
                      ((i + (Prims.parse_int "1")), uu____3736)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3717 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3757 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3765  ->
                                match uu____3765 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____3757 with
                       | (uu____3778,u_let_rec_closing) ->
                           let uu___145_3782 = lb in
                           let uu____3783 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___145_3782.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___145_3782.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___145_3782.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___145_3782.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3783
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3793  ->
      match uu____3793 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3811  ->
                   match uu____3811 with
                   | (x,uu____3815) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3826  ->
      match uu____3826 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____3844 = subst s t in (us', uu____3844)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3859  ->
              match uu____3859 with
              | (x,uu____3863) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3877  ->
              match uu____3877 with
              | (x,uu____3881) -> FStar_Syntax_Syntax.NM (x, (n1 - i))))