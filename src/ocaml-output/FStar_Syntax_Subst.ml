open Prims
let subst_to_string s =
  let uu____16 =
    FStar_All.pipe_right s
      (FStar_List.map
         (fun uu____24  ->
            match uu____24 with
            | (b,uu____28) ->
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____16 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> None
  | s0::rest ->
      let uu____67 = f s0 in
      (match uu____67 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
let map_some_curry f x uu___110_113 =
  match uu___110_113 with | None  -> x | Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____181 = apply_until_some f s in
  FStar_All.pipe_right uu____181 (map_some_curry g t)
let compose_subst s1 s2 =
  let s = FStar_List.append (fst s1) (fst s2) in
  let ropt =
    match snd s2 with | Some uu____240 -> snd s2 | uu____243 -> snd s1 in
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
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____311 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____332) ->
        let uu____345 = FStar_Syntax_Unionfind.find uv in
        (match uu____345 with | Some t' -> force_uvar' t' | uu____350 -> t)
    | uu____352 -> t
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____366 = FStar_Util.physical_equality t t' in
    if uu____366
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
        let uu____414 = FStar_ST.read m in
        (match uu____414 with
         | None  -> t
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____443 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____451 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____451 with | Some u1 -> compress_univ u1 | uu____454 -> u)
    | uu____456 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___111_468  ->
           match uu___111_468 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____472 =
                 let uu____473 =
                   let uu____474 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____474 in
                 FStar_Syntax_Syntax.bv_to_name uu____473 in
               Some uu____472
           | uu____475 -> None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___112_487  ->
           match uu___112_487 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____491 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___116_492 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___116_492.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___116_492.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____491
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____501 -> None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___113_513  ->
           match uu___113_513 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____517 -> None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___114_529  ->
           match uu___114_529 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____533 -> None)
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
      | FStar_Syntax_Syntax.U_unif uu____551 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____555 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____555
      | FStar_Syntax_Syntax.U_max us ->
          let uu____558 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____558
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu____595 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____595
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____597 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____597
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___117_605 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.ty =
                  (uu___117_605.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___117_605.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___118_621 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___118_621.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___118_621.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___119_623 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___119_623.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___119_623.FStar_Syntax_Syntax.vars)
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
      let uu____653 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____653
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
      | uu____737 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____745 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____748 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____751 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____817 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____818 =
                 let uu____821 =
                   let uu____822 = subst_univ (fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____822 in
                 FStar_Syntax_Syntax.mk uu____821 in
               uu____818 None uu____817
           | uu____834 ->
               let uu____835 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____835)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___115_843  ->
              match uu___115_843 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____847 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____847
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
      | uu____867 ->
          let uu___120_873 = t in
          let uu____874 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____878 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____881 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____884 =
            FStar_List.map
              (fun uu____898  ->
                 match uu____898 with
                 | (t1,imp) ->
                     let uu____913 = subst' s t1 in (uu____913, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____918 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____874;
            FStar_Syntax_Syntax.effect_name = uu____878;
            FStar_Syntax_Syntax.result_typ = uu____881;
            FStar_Syntax_Syntax.effect_args = uu____884;
            FStar_Syntax_Syntax.flags = uu____918
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
      | uu____940 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____956 = subst' s t1 in
               let uu____957 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____956 uu____957
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____970 = subst' s t1 in
               let uu____971 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____970 uu____971
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____977 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____977)
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
      | FStar_Syntax_Syntax.NT uu____994 -> s
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
  let uu____1031 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1031, (snd s))
let subst_binder' s uu____1056 =
  match uu____1056 with
  | (x,imp) ->
      let uu____1061 =
        let uu___121_1062 = x in
        let uu____1063 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___121_1062.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___121_1062.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1063
        } in
      (uu____1061, imp)
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
              (let uu____1107 = shift_subst' i s in
               subst_binder' uu____1107 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
let subst_arg' s uu____1146 =
  match uu____1146 with
  | (t,imp) -> let uu____1157 = subst' s t in (uu____1157, imp)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1233 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1248 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1273  ->
                      fun uu____1274  ->
                        match (uu____1273, uu____1274) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1321 = aux n2 p2 in
                            (match uu____1321 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1248 with
             | (pats1,n2) ->
                 ((let uu___122_1353 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.ty =
                       (uu___122_1353.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___122_1353.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___123_1369 = x in
              let uu____1370 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___123_1369.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___123_1369.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1370
              } in
            ((let uu___124_1375 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.ty =
                  (uu___124_1375.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___124_1375.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___125_1386 = x in
              let uu____1387 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___125_1386.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___125_1386.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1387
              } in
            ((let uu___126_1392 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.ty =
                  (uu___126_1392.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___126_1392.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___127_1408 = x in
              let uu____1409 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___127_1408.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___127_1408.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1409
              } in
            let t01 = subst' s1 t0 in
            ((let uu___128_1417 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.ty =
                  (uu___128_1417.FStar_Syntax_Syntax.ty);
                FStar_Syntax_Syntax.p = (uu___128_1417.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp option ->
      FStar_Syntax_Syntax.residual_comp option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | None  -> None
      | Some rc ->
          let uu____1435 =
            let uu___129_1436 = rc in
            let uu____1437 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___129_1436.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1437;
              FStar_Syntax_Syntax.residual_flags =
                (uu___129_1436.FStar_Syntax_Syntax.residual_flags)
            } in
          Some uu____1435
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
        let uu____1465 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1465 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1472 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1489 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1492 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1497 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1508 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1509 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1510 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1522 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1522 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1543 =
            let uu____1544 =
              let uu____1554 = subst' s t0 in
              let uu____1557 = subst_args' s args in (uu____1554, uu____1557) in
            FStar_Syntax_Syntax.Tm_app uu____1544 in
          mk1 uu____1543
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____1629 = subst' s t1 in FStar_Util.Inl uu____1629
            | FStar_Util.Inr c ->
                let uu____1643 = subst_comp' s c in FStar_Util.Inr uu____1643 in
          let uu____1650 =
            let uu____1651 =
              let uu____1669 = subst' s t0 in
              let uu____1672 =
                let uu____1684 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1684) in
              (uu____1669, uu____1672, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1651 in
          mk1 uu____1650
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1745 =
            let uu____1746 =
              let uu____1756 = subst_binders' s bs in
              let uu____1760 = subst' s' body in
              let uu____1763 = push_subst_lcomp s' lopt in
              (uu____1756, uu____1760, uu____1763) in
            FStar_Syntax_Syntax.Tm_abs uu____1746 in
          mk1 uu____1745
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1788 =
            let uu____1789 =
              let uu____1797 = subst_binders' s bs in
              let uu____1801 =
                let uu____1804 = shift_subst' n1 s in
                subst_comp' uu____1804 comp in
              (uu____1797, uu____1801) in
            FStar_Syntax_Syntax.Tm_arrow uu____1789 in
          mk1 uu____1788
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___130_1827 = x in
            let uu____1828 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_1827.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_1827.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1828
            } in
          let phi1 =
            let uu____1834 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____1834 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____1917  ->
                    match uu____1917 with
                    | (pat,wopt,branch) ->
                        let uu____1953 = subst_pat' s pat in
                        (match uu____1953 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
                                   let uu____1988 = subst' s1 w in
                                   Some uu____1988 in
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
                      let uu____2051 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2051
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___131_2061 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___131_2061.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___131_2061.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv ->
                          FStar_Util.Inr
                            (let uu___132_2063 = fv in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (let uu___133_2064 =
                                    fv.FStar_Syntax_Syntax.fv_name in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (uu___133_2064.FStar_Syntax_Syntax.v);
                                    FStar_Syntax_Syntax.ty = lbt;
                                    FStar_Syntax_Syntax.p =
                                      (uu___133_2064.FStar_Syntax_Syntax.p)
                                  });
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___132_2063.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual =
                                 (uu___132_2063.FStar_Syntax_Syntax.fv_qual)
                             }) in
                    let uu___134_2079 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___134_2079.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___134_2079.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2098 =
            let uu____2099 =
              let uu____2104 = subst' s t0 in
              let uu____2107 =
                let uu____2108 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2108 in
              (uu____2104, uu____2107) in
            FStar_Syntax_Syntax.Tm_meta uu____2099 in
          mk1 uu____2098
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2150 =
            let uu____2151 =
              let uu____2156 = subst' s t0 in
              let uu____2159 =
                let uu____2160 =
                  let uu____2165 = subst' s t1 in (m, uu____2165) in
                FStar_Syntax_Syntax.Meta_monadic uu____2160 in
              (uu____2156, uu____2159) in
            FStar_Syntax_Syntax.Tm_meta uu____2151 in
          mk1 uu____2150
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2184 =
            let uu____2185 =
              let uu____2190 = subst' s t0 in
              let uu____2193 =
                let uu____2194 =
                  let uu____2200 = subst' s t1 in (m1, m2, uu____2200) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2194 in
              (uu____2190, uu____2193) in
            FStar_Syntax_Syntax.Tm_meta uu____2185 in
          mk1 uu____2184
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2213 =
            let uu____2214 = let uu____2219 = subst' s t1 in (uu____2219, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2214 in
          mk1 uu____2213
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____2264 = push_subst s t2 in compress uu____2264 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2271 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2275 -> compress t'
         | uu____2290 -> t')
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
             (let uu___135_2318 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___135_2318.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____2339 =
      FStar_List.fold_right
        (fun uu____2348  ->
           fun uu____2349  ->
             match (uu____2348, uu____2349) with
             | ((x,uu____2364),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____2339 FStar_Pervasives.fst
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
          let uu___136_2446 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2447 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___136_2446.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___136_2446.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2447
          } in
        let o1 =
          let uu____2452 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2452 in
        let uu____2454 = aux bs' o1 in
        (match uu____2454 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun bs  -> let uu____2487 = open_binders' bs in fst uu____2487
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
      let uu____2509 = open_binders' bs in
      match uu____2509 with
      | (bs',opening) ->
          let uu____2529 = subst opening t in (bs', uu____2529, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      let uu____2544 = open_term' bs t in
      match uu____2544 with | (b,t1,uu____2552) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
      let uu____2563 = open_binders' bs in
      match uu____2563 with
      | (bs',opening) ->
          let uu____2582 = subst_comp opening t in (bs', uu____2582)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____2634 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2653 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2699  ->
                    fun uu____2700  ->
                      match (uu____2699, uu____2700) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2788 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2788 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2653 with
           | (pats1,sub2,renaming1) ->
               ((let uu___137_2889 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___137_2889.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___137_2889.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___138_2903 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2904 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_2903.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_2903.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2904
            } in
          let sub2 =
            let uu____2909 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2909 in
          ((let uu___139_2917 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.ty = (uu___139_2917.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___139_2917.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___140_2924 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____2925 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_2924.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_2924.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2925
            } in
          let sub2 =
            let uu____2930 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____2930 in
          ((let uu___141_2938 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.ty = (uu___141_2938.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___141_2938.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_2950 = x in
            let uu____2951 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_2950.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_2950.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2951
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_2961 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___143_2961.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___143_2961.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____2964 = open_pat_aux [] [] p in
    match uu____2964 with | (p1,sub1,uu____2980) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____2999  ->
    match uu____2999 with
    | (p,wopt,e) ->
        let uu____3017 = open_pat p in
        (match uu____3017 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3032 = subst opening w in Some uu____3032 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____3043 = closing_subst bs in subst uu____3043 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____3053 = closing_subst bs in subst_comp uu____3053 c
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
            let uu___144_3087 = x in
            let uu____3088 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___144_3087.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___144_3087.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3088
            } in
          let s' =
            let uu____3093 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3093 in
          let uu____3095 = aux s' tl1 in (x1, imp) :: uu____3095 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___145_3111 = lc in
      let uu____3112 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___145_3111.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3112;
        FStar_Syntax_Syntax.cflags =
          (uu___145_3111.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3115  ->
             let uu____3116 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3116)
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
      | FStar_Syntax_Syntax.Pat_constant uu____3153 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3169 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3203  ->
                    fun uu____3204  ->
                      match (uu____3203, uu____3204) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3269 = aux sub2 p2 in
                          (match uu____3269 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3169 with
           | (pats1,sub2) ->
               ((let uu___146_3335 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.ty =
                     (uu___146_3335.FStar_Syntax_Syntax.ty);
                   FStar_Syntax_Syntax.p =
                     (uu___146_3335.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___147_3349 = x in
            let uu____3350 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___147_3349.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___147_3349.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3350
            } in
          let sub2 =
            let uu____3355 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3355 in
          ((let uu___148_3360 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.ty = (uu___148_3360.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___148_3360.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___149_3365 = x in
            let uu____3366 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___149_3365.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___149_3365.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3366
            } in
          let sub2 =
            let uu____3371 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3371 in
          ((let uu___150_3376 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.ty = (uu___150_3376.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___150_3376.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___151_3386 = x in
            let uu____3387 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___151_3386.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___151_3386.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3387
            } in
          let t01 = subst sub1 t0 in
          ((let uu___152_3394 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.ty = (uu___152_3394.FStar_Syntax_Syntax.ty);
              FStar_Syntax_Syntax.p = (uu___152_3394.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3400  ->
    match uu____3400 with
    | (p,wopt,e) ->
        let uu____3418 = close_pat p in
        (match uu____3418 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
                   let uu____3442 = subst closing w in Some uu____3442 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let uu____3462 =
      let uu____3467 =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
      FStar_All.pipe_right uu____3467 FStar_List.unzip in
    match uu____3462 with | (s,us') -> (s, us')
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
      let uu____3510 = univ_var_opening us in
      match uu____3510 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let uu____3537 = univ_var_opening us in
      match uu____3537 with
      | (s,us') -> let uu____3550 = subst_comp s c in (us', uu____3550)
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
      let uu____3605 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3605
      then (lbs, t)
      else
        (let uu____3611 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3623  ->
                  match uu____3623 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3642 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3642 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___153_3645 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___153_3645.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___153_3645.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___153_3645.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___153_3645.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3611 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3663 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3675  ->
                                match uu____3675 with
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
                       match uu____3663 with
                       | (uu____3698,us,u_let_rec_opening) ->
                           let uu___154_3705 = lb in
                           let uu____3706 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___154_3705.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___154_3705.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___154_3705.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3706
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
      let uu____3724 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3724
      then (lbs, t)
      else
        (let uu____3730 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3738  ->
                  match uu____3738 with
                  | (i,out) ->
                      let uu____3749 =
                        let uu____3751 =
                          let uu____3752 =
                            let uu____3755 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3755, i) in
                          FStar_Syntax_Syntax.NM uu____3752 in
                        uu____3751 :: out in
                      ((i + (Prims.parse_int "1")), uu____3749)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3730 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____3770 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3778  ->
                                match uu____3778 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
                       match uu____3770 with
                       | (uu____3791,u_let_rec_closing) ->
                           let uu___155_3795 = lb in
                           let uu____3796 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___155_3795.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_3795.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___155_3795.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_3795.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3796
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
    fun uu____3808  ->
      match uu____3808 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____3830  ->
                   match uu____3830 with
                   | (x,uu____3834) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun uu____3850  ->
      match uu____3850 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____3875 = subst s t in (us', uu____3875)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____3894  ->
              match uu____3894 with
              | (x,uu____3898) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))