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
              let uu___109_673 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___109_673.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___109_673.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___110_689 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___110_689.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___110_689.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___111_691 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___111_691.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___111_691.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____718 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____718
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
      | uu____800 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____808 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____811 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____814 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____897,uu____898) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____954 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____955 =
                 let uu____958 =
                   let uu____959 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____959 in
                 FStar_Syntax_Syntax.mk uu____958 in
               uu____955 None uu____954
           | uu____971 ->
               let uu____972 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t0, s))
                 uu____972)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___107_986  ->
              match uu___107_986 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____990 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____990
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
      | uu____1010 ->
          let uu___112_1016 = t in
          let uu____1017 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1021 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1024 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1027 =
            FStar_List.map
              (fun uu____1041  ->
                 match uu____1041 with
                 | (t1,imp) ->
                     let uu____1056 = subst' s t1 in (uu____1056, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1061 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1017;
            FStar_Syntax_Syntax.effect_name = uu____1021;
            FStar_Syntax_Syntax.result_typ = uu____1024;
            FStar_Syntax_Syntax.effect_args = uu____1027;
            FStar_Syntax_Syntax.flags = uu____1061
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
      | uu____1083 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1099 = subst' s t1 in
               let uu____1100 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1099 uu____1100
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1113 = subst' s t1 in
               let uu____1114 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1113 uu____1114
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1120 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1120)
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
      | FStar_Syntax_Syntax.NT uu____1135 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1167 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1167, (snd s))
let subst_binder' s uu____1189 =
  match uu____1189 with
  | (x,imp) ->
      let uu____1194 =
        let uu___113_1195 = x in
        let uu____1196 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___113_1195.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___113_1195.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1196
        } in
      (uu____1194, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1237 = shift_subst' i s in
               subst_binder' uu____1237 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1271 =
  match uu____1271 with
  | (t,imp) -> let uu____1282 = subst' s t in (uu____1282, imp)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1353 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1368 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1393  ->
                      fun uu____1394  ->
                        match (uu____1393, uu____1394) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1441 = aux n2 p2 in
                            (match uu____1441 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1368 with
             | (pats1,n2) ->
                 ((let uu___114_1473 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___114_1473.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___114_1473.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___115_1489 = x in
              let uu____1490 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1489.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1489.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1490
              } in
            ((let uu___116_1495 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___116_1495.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___116_1495.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___117_1506 = x in
              let uu____1507 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___117_1506.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___117_1506.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1507
              } in
            ((let uu___118_1512 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___118_1512.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___118_1512.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___119_1528 = x in
              let uu____1529 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1528.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1528.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1529
              } in
            let t01 = subst' s1 t0 in
            ((let uu___120_1537 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___120_1537.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___120_1537.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp s lopt =
  match lopt with
  | None  -> lopt
  | Some (FStar_Util.Inr uu____1565) -> lopt
  | Some (FStar_Util.Inl l) ->
      let uu____1571 =
        let uu____1574 =
          let uu___121_1575 = l in
          let uu____1576 = subst' s l.FStar_Syntax_Syntax.res_typ in
          {
            FStar_Syntax_Syntax.eff_name =
              (uu___121_1575.FStar_Syntax_Syntax.eff_name);
            FStar_Syntax_Syntax.res_typ = uu____1576;
            FStar_Syntax_Syntax.cflags =
              (uu___121_1575.FStar_Syntax_Syntax.cflags);
            FStar_Syntax_Syntax.comp =
              (fun uu____1579  ->
                 let uu____1580 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1580)
          } in
        FStar_Util.Inl uu____1574 in
      Some uu____1571
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
        let uu____1603 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1603 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1610 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1633 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1636 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1641 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1654 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1655 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1656 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1668 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1668 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1689 =
            let uu____1690 =
              let uu____1700 = subst' s t0 in
              let uu____1703 = subst_args' s args in (uu____1700, uu____1703) in
            FStar_Syntax_Syntax.Tm_app uu____1690 in
          mk1 uu____1689
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1775 = subst' s t1 in FStar_Util.Inl uu____1775
            | FStar_Util.Inr c ->
                let uu____1789 = subst_comp' s c in FStar_Util.Inr uu____1789 in
          let uu____1796 =
            let uu____1797 =
              let uu____1815 = subst' s t0 in
              let uu____1818 =
                let uu____1830 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1830) in
              (uu____1815, uu____1818, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1797 in
          mk1 uu____1796
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1898 =
            let uu____1899 =
              let uu____1914 = subst_binders' s bs in
              let uu____1918 = subst' s' body in
              let uu____1921 = push_subst_lcomp s' lopt in
              (uu____1914, uu____1918, uu____1921) in
            FStar_Syntax_Syntax.Tm_abs uu____1899 in
          mk1 uu____1898
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1958 =
            let uu____1959 =
              let uu____1967 = subst_binders' s bs in
              let uu____1971 =
                let uu____1974 = shift_subst' n1 s in
                subst_comp' uu____1974 comp in
              (uu____1967, uu____1971) in
            FStar_Syntax_Syntax.Tm_arrow uu____1959 in
          mk1 uu____1958
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___122_1995 = x in
            let uu____1996 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_1995.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1995.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1996
            } in
          let phi1 =
            let uu____2002 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2002 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2085  ->
                    match uu____2085 with
                    | (pat,wopt,branch) ->
                        let uu____2121 = subst_pat' s pat in
                        (match uu____2121 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____2156 = subst' s1 w in
                                   Some uu____2156 in
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
                      let uu____2216 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2216
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___123_2226 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2226.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2226.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___124_2228 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___125_2229 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___125_2229.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___125_2229.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___124_2228.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___124_2228.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___126_2244 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___126_2244.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___126_2244.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2263 =
            let uu____2264 =
              let uu____2269 = subst' s t0 in
              let uu____2272 =
                let uu____2273 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2273 in
              (uu____2269, uu____2272) in
            FStar_Syntax_Syntax.Tm_meta uu____2264 in
          mk1 uu____2263
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2315 =
            let uu____2316 =
              let uu____2321 = subst' s t0 in
              let uu____2324 =
                let uu____2325 =
                  let uu____2330 = subst' s t1 in (m, uu____2330) in
                FStar_Syntax_Syntax.Meta_monadic uu____2325 in
              (uu____2321, uu____2324) in
            FStar_Syntax_Syntax.Tm_meta uu____2316 in
          mk1 uu____2315
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2349 =
            let uu____2350 =
              let uu____2355 = subst' s t0 in
              let uu____2358 =
                let uu____2359 =
                  let uu____2365 = subst' s t1 in (m1, m2, uu____2365) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2359 in
              (uu____2355, uu____2358) in
            FStar_Syntax_Syntax.Tm_meta uu____2350 in
          mk1 uu____2349
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2378 =
            let uu____2379 = let uu____2384 = subst' s t1 in (uu____2384, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2379 in
          mk1 uu____2378
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2447 = push_subst s t2 in compress uu____2447 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2454 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2458 -> compress t'
         | uu____2479 -> t')
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
             (let uu___127_2503 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___127_2503.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst bs =
  let uu____2531 =
    FStar_List.fold_right
      (fun uu____2540  ->
         fun uu____2541  ->
           match (uu____2540, uu____2541) with
           | ((x,uu____2556),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2531 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___128_2636 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2637 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___128_2636.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___128_2636.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2637
          } in
        let o1 =
          let uu____2642 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2642 in
        let uu____2644 = aux bs' o1 in
        (match uu____2644 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2676 = open_binders' bs in fst uu____2676
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2696 = open_binders' bs in
      match uu____2696 with
      | (bs',opening) ->
          let uu____2716 = subst opening t in (bs', uu____2716, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2729 = open_term' bs t in
      match uu____2729 with | (b,t1,uu____2737) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2746 = open_binders' bs in
      match uu____2746 with
      | (bs',opening) ->
          let uu____2765 = subst_comp opening t in (bs', uu____2765)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2816 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2835 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2881  ->
                    fun uu____2882  ->
                      match (uu____2881, uu____2882) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2970 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2970 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2835 with
           | (pats1,sub2,renaming1) ->
               ((let uu___129_3071 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___129_3071.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___129_3071.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___130_3085 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3086 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_3085.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_3085.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3086
            } in
          let sub2 =
            let uu____3091 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3091 in
          ((let uu___131_3099 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___131_3099.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___131_3099.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___132_3106 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3107 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_3106.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_3106.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3107
            } in
          let sub2 =
            let uu____3112 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3112 in
          ((let uu___133_3120 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___133_3120.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___133_3120.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___134_3132 = x in
            let uu____3133 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_3132.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_3132.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3133
            } in
          let t01 = subst sub1 t0 in
          ((let uu___135_3143 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___135_3143.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___135_3143.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3146 = open_pat_aux [] [] p in
    match uu____3146 with | (p1,sub1,uu____3162) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3180  ->
    match uu____3180 with
    | (p,wopt,e) ->
        let uu____3198 = open_pat p in
        (match uu____3198 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3213 = subst opening w in Some uu____3213 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3222 = closing_subst bs in subst uu____3222 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3230 = closing_subst bs in subst_comp uu____3230 c
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
            let uu___136_3263 = x in
            let uu____3264 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_3263.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_3263.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3264
            } in
          let s' =
            let uu____3269 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3269 in
          let uu____3271 = aux s' tl1 in (x1, imp) :: uu____3271 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___137_3285 = lc in
      let uu____3286 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___137_3285.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3286;
        FStar_Syntax_Syntax.cflags =
          (uu___137_3285.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3289  ->
             let uu____3290 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3290)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3326 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3342 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3376  ->
                    fun uu____3377  ->
                      match (uu____3376, uu____3377) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3442 = aux sub2 p2 in
                          (match uu____3442 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3342 with
           | (pats1,sub2) ->
               ((let uu___138_3508 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___138_3508.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___138_3508.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___139_3522 = x in
            let uu____3523 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3522.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3522.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3523
            } in
          let sub2 =
            let uu____3528 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3528 in
          ((let uu___140_3533 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___140_3533.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___140_3533.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___141_3538 = x in
            let uu____3539 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3538.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3538.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3539
            } in
          let sub2 =
            let uu____3544 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3544 in
          ((let uu___142_3549 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___142_3549.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___142_3549.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___143_3559 = x in
            let uu____3560 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___143_3559.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___143_3559.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3560
            } in
          let t01 = subst sub1 t0 in
          ((let uu___144_3567 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___144_3567.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___144_3567.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3572  ->
    match uu____3572 with
    | (p,wopt,e) ->
        let uu____3590 = close_pat p in
        (match uu____3590 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3614 = subst closing w in Some uu____3614 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3630 =
      let uu____3635 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3635 FStar_List.unzip in
    match uu____3630 with | (s,us') -> (s, us')
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
      let uu____3687 = univ_var_opening us in
      match uu____3687 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3712 = univ_var_opening us in
      match uu____3712 with
      | (s,us') -> let uu____3725 = subst_comp s c in (us', uu____3725)
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
      let uu____3761 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3761
      then (lbs, t)
      else
        (let uu____3767 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3779  ->
                  match uu____3779 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3798 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3798 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___145_3801 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___145_3801.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___145_3801.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___145_3801.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___145_3801.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3767 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3819 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3831  ->
                                match uu____3831 with
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
                       match uu____3819 with
                       | (uu____3854,us,u_let_rec_opening) ->
                           let uu___146_3861 = lb in
                           let uu____3862 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___146_3861.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___146_3861.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___146_3861.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3862
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3878 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3878
      then (lbs, t)
      else
        (let uu____3884 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3892  ->
                  match uu____3892 with
                  | (i,out) ->
                      let uu____3903 =
                        let uu____3905 =
                          let uu____3906 =
                            let uu____3909 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3909, i) in
                          FStar_Syntax_Syntax.NM uu____3906 in
                        uu____3905 :: out in
                      ((i + (Prims.parse_int "1")), uu____3903)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3884 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3924 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3932  ->
                                match uu____3932 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____3924 with
                       | (uu____3945,u_let_rec_closing) ->
                           let uu___147_3949 = lb in
                           let uu____3950 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___147_3949.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___147_3949.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___147_3949.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___147_3949.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3950
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3960  ->
      match uu____3960 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3978  ->
                   match uu____3978 with
                   | (x,uu____3982) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3993  ->
      match uu____3993 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____4011 = subst s t in (us', uu____4011)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4026  ->
              match uu____4026 with
              | (x,uu____4030) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4044  ->
              match uu____4044 with
              | (x,uu____4048) -> FStar_Syntax_Syntax.NM (x, (n1 - i))))