open Prims
let subst_to_string s =
  let uu____16 =
    FStar_All.pipe_right s
      (FStar_List.map
<<<<<<< HEAD
         (fun uu____25  ->
            match uu____25 with
            | (b,uu____29) ->
=======
         (fun uu____24  ->
            match uu____24 with
            | (b,uu____28) ->
>>>>>>> origin/guido_tactics
                (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
  FStar_All.pipe_right uu____16 (FStar_String.concat ", ")
let rec apply_until_some f s =
  match s with
  | [] -> None
  | s0::rest ->
<<<<<<< HEAD
      let uu____64 = f s0 in
      (match uu____64 with
       | None  -> apply_until_some f rest
       | Some st -> Some (rest, st))
let map_some_curry f x uu___102_104 =
  match uu___102_104 with | None  -> x | Some (a,b) -> f a b
let apply_until_some_then_map f s g t =
  let uu____165 = apply_until_some f s in
  FStar_All.pipe_right uu____165 (map_some_curry g t)
let compose_subst s1 s2 =
  let s = FStar_List.append (fst s1) (fst s2) in
  let ropt =
    match snd s2 with | Some uu____220 -> snd s2 | uu____223 -> snd s1 in
=======
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
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed
            (FStar_Util.Inl (t', (compose_subst s' s)))
            t.FStar_Syntax_Syntax.pos
      | uu____319 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (t, s))
=======
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____350) ->
        let uu____367 = FStar_Syntax_Unionfind.find uv in
        (match uu____367 with | Some t' -> force_uvar' t' | uu____372 -> t)
    | uu____374 -> t
=======
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____332) ->
        let uu____345 = FStar_Syntax_Unionfind.find uv in
        (match uu____345 with | Some t' -> force_uvar' t' | uu____350 -> t)
    | uu____352 -> t
>>>>>>> origin/guido_tactics
let force_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t in
<<<<<<< HEAD
    let uu____387 = FStar_Util.physical_equality t t' in
    if uu____387
=======
    let uu____366 = FStar_Util.physical_equality t t' in
    if uu____366
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____446 = FStar_ST.read m in
        (match uu____446 with
         | None  ->
             (match f with
              | FStar_Util.Inr c ->
                  let t' =
                    let uu____482 = c () in force_delayed_thunk uu____482 in
                  (FStar_ST.write m (Some t'); t')
              | uu____493 -> t)
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____525 -> t
=======
        let uu____414 = FStar_ST.read m in
        (match uu____414 with
         | None  -> t
         | Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.write m (Some t'1); t'1))
    | uu____443 -> t
>>>>>>> origin/guido_tactics
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
<<<<<<< HEAD
        let uu____534 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____534 with | Some u1 -> compress_univ u1 | uu____537 -> u)
    | uu____539 -> u
=======
        let uu____451 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____451 with | Some u1 -> compress_univ u1 | uu____454 -> u)
    | uu____456 -> u
>>>>>>> origin/guido_tactics
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
<<<<<<< HEAD
        (fun uu___103_553  ->
           match uu___103_553 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____557 =
                 let uu____558 =
                   let uu____559 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____559 in
                 FStar_Syntax_Syntax.bv_to_name uu____558 in
               Some uu____557
           | uu____560 -> None)
=======
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
>>>>>>> origin/guido_tactics
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
<<<<<<< HEAD
        (fun uu___104_574  ->
           match uu___104_574 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____578 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___108_581 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___108_581.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___108_581.FStar_Syntax_Syntax.sort)
                    }) in
               Some uu____578
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> Some t
           | uu____590 -> None)
=======
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
>>>>>>> origin/guido_tactics
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
<<<<<<< HEAD
        (fun uu___105_603  ->
           match uu___105_603 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____607 -> None)
=======
        (fun uu___113_513  ->
           match uu___113_513 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y -> Some t
           | uu____517 -> None)
>>>>>>> origin/guido_tactics
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
<<<<<<< HEAD
        (fun uu___106_620  ->
           match uu___106_620 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____624 -> None)
=======
        (fun uu___114_529  ->
           match uu___114_529 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____533 -> None)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | FStar_Syntax_Syntax.U_unif uu____640 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____646 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____646
      | FStar_Syntax_Syntax.U_max us ->
          let uu____649 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____649
=======
      | FStar_Syntax_Syntax.U_unif uu____551 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____555 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____555
      | FStar_Syntax_Syntax.U_max us ->
          let uu____558 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____558
>>>>>>> origin/guido_tactics
let tag_with_range t s =
  match snd s with
  | None  -> t
  | Some r ->
      let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
      let t' =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_bvar bv ->
<<<<<<< HEAD
            let uu____682 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_bvar uu____682
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu____684 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
            FStar_Syntax_Syntax.Tm_name uu____684
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv in
            let v1 =
              let uu___109_689 = fv.FStar_Syntax_Syntax.fv_name in
              {
                FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                FStar_Syntax_Syntax.p = (uu___109_689.FStar_Syntax_Syntax.p)
              } in
            let fv1 =
              let uu___110_691 = fv in
              {
                FStar_Syntax_Syntax.fv_name = v1;
                FStar_Syntax_Syntax.fv_delta =
                  (uu___110_691.FStar_Syntax_Syntax.fv_delta);
                FStar_Syntax_Syntax.fv_qual =
                  (uu___110_691.FStar_Syntax_Syntax.fv_qual)
              } in
            FStar_Syntax_Syntax.Tm_fvar fv1
        | t' -> t' in
      let uu___111_693 = t in
      {
        FStar_Syntax_Syntax.n = t';
        FStar_Syntax_Syntax.tk = (uu___111_693.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = r1;
        FStar_Syntax_Syntax.vars = (uu___111_693.FStar_Syntax_Syntax.vars)
=======
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
>>>>>>> origin/guido_tactics
      }
let tag_lid_with_range l s =
  match snd s with
  | None  -> l
  | Some r ->
<<<<<<< HEAD
      let uu____720 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____720
=======
      let uu____653 =
        FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
      FStar_Ident.set_lid_range l uu____653
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____802 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____810 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____813 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____816 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed
                 (FStar_Util.Inl (t', (compose_subst s' s)))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_delayed
               (FStar_Util.Inr uu____899,uu____900) ->
               failwith
                 "Impossible: force_delayed_thunk removes lazy delayed nodes"
=======
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
>>>>>>> origin/guido_tactics
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a) (fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
<<<<<<< HEAD
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
=======
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
>>>>>>> origin/guido_tactics
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
<<<<<<< HEAD
           (fun uu___107_991  ->
              match uu___107_991 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____995 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____995
=======
           (fun uu___115_843  ->
              match uu___115_843 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____847 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____847
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____1015 ->
          let uu___112_1021 = t in
          let uu____1022 =
            FStar_List.map (subst_univ (fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1026 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1029 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1032 =
            FStar_List.map
              (fun uu____1050  ->
                 match uu____1050 with
                 | (t1,imp) ->
                     let uu____1065 = subst' s t1 in (uu____1065, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1070 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1022;
            FStar_Syntax_Syntax.effect_name = uu____1026;
            FStar_Syntax_Syntax.result_typ = uu____1029;
            FStar_Syntax_Syntax.effect_args = uu____1032;
            FStar_Syntax_Syntax.flags = uu____1070
=======
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
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____1092 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1108 = subst' s t1 in
               let uu____1109 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1108 uu____1109
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1122 = subst' s t1 in
               let uu____1123 = FStar_Option.map (subst_univ (fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1122 uu____1123
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1129 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1129)
=======
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
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | FStar_Syntax_Syntax.NT uu____1144 -> s
=======
      | FStar_Syntax_Syntax.NT uu____994 -> s
>>>>>>> origin/guido_tactics
let shift_subst:
  Prims.int ->
    FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_elt Prims.list
  = fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' n1 s =
<<<<<<< HEAD
  let uu____1176 =
    FStar_All.pipe_right (fst s) (FStar_List.map (shift_subst n1)) in
  (uu____1176, (snd s))
let subst_binder' s uu____1198 =
  match uu____1198 with
  | (x,imp) ->
      let uu____1203 =
        let uu___113_1204 = x in
        let uu____1205 = subst' s x.FStar_Syntax_Syntax.sort in
        {
          FStar_Syntax_Syntax.ppname =
            (uu___113_1204.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index =
            (uu___113_1204.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = uu____1205
        } in
      (uu____1203, imp)
=======
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
>>>>>>> origin/guido_tactics
let subst_binders' s bs =
  FStar_All.pipe_right bs
    (FStar_List.mapi
       (fun i  ->
          fun b  ->
            if i = (Prims.parse_int "0")
            then subst_binder' s b
            else
<<<<<<< HEAD
              (let uu____1248 = shift_subst' i s in
               subst_binder' uu____1248 b)))
=======
              (let uu____1107 = shift_subst' i s in
               subst_binder' uu____1107 b)))
>>>>>>> origin/guido_tactics
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  = fun s  -> fun bs  -> subst_binders' ([s], None) bs
<<<<<<< HEAD
let subst_arg' s uu____1282 =
  match uu____1282 with
  | (t,imp) -> let uu____1293 = subst' s t in (uu____1293, imp)
=======
let subst_arg' s uu____1146 =
  match uu____1146 with
  | (t,imp) -> let uu____1157 = subst' s t in (uu____1157, imp)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        | FStar_Syntax_Syntax.Pat_constant uu____1358 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1370 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1402  ->
                      fun uu____1403  ->
                        match (uu____1402, uu____1403) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1445 = aux n2 p2 in
                            (match uu____1445 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1370 with
             | (pats1,n2) ->
                 ((let uu___114_1477 = p1 in
=======
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
>>>>>>> origin/guido_tactics
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
<<<<<<< HEAD
                     FStar_Syntax_Syntax.p =
                       (uu___114_1477.FStar_Syntax_Syntax.p)
=======
                     FStar_Syntax_Syntax.ty =
                       (uu___122_1353.FStar_Syntax_Syntax.ty);
                     FStar_Syntax_Syntax.p =
                       (uu___122_1353.FStar_Syntax_Syntax.p)
>>>>>>> origin/guido_tactics
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
<<<<<<< HEAD
              let uu___115_1492 = x in
              let uu____1493 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___115_1492.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___115_1492.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1493
              } in
            ((let uu___116_1498 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___116_1498.FStar_Syntax_Syntax.p)
=======
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
>>>>>>> origin/guido_tactics
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
<<<<<<< HEAD
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
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___118_1514.FStar_Syntax_Syntax.p)
=======
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
>>>>>>> origin/guido_tactics
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
<<<<<<< HEAD
              let uu___119_1529 = x in
              let uu____1530 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___119_1529.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___119_1529.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1530
              } in
            let t01 = subst' s1 t0 in
            ((let uu___120_1538 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___120_1538.FStar_Syntax_Syntax.p)
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
              (fun uu____1581  ->
                 let uu____1582 = l.FStar_Syntax_Syntax.comp () in
                 subst_comp' s uu____1582)
          } in
        FStar_Util.Inl uu____1574 in
      Some uu____1571
=======
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
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____1605 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' None uu____1605 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____1612 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____1635 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____1638 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____1643 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____1656 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____1657 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____1658 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 = FStar_List.map (subst_univ (fst s)) us in
          let uu____1670 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____1670 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____1691 =
            let uu____1692 =
              let uu____1702 = subst' s t0 in
              let uu____1705 = subst_args' s args in (uu____1702, uu____1705) in
            FStar_Syntax_Syntax.Tm_app uu____1692 in
          mk1 uu____1691
=======
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
>>>>>>> origin/guido_tactics
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
<<<<<<< HEAD
                let uu____1777 = subst' s t1 in FStar_Util.Inl uu____1777
            | FStar_Util.Inr c ->
                let uu____1791 = subst_comp' s c in FStar_Util.Inr uu____1791 in
          let uu____1798 =
            let uu____1799 =
              let uu____1817 = subst' s t0 in
              let uu____1820 =
                let uu____1832 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____1832) in
              (uu____1817, uu____1820, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____1799 in
          mk1 uu____1798
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____1900 =
            let uu____1901 =
              let uu____1916 = subst_binders' s bs in
              let uu____1920 = subst' s' body in
              let uu____1923 = push_subst_lcomp s' lopt in
              (uu____1916, uu____1920, uu____1923) in
            FStar_Syntax_Syntax.Tm_abs uu____1901 in
          mk1 uu____1900
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____1960 =
            let uu____1961 =
              let uu____1969 = subst_binders' s bs in
              let uu____1973 =
                let uu____1976 = shift_subst' n1 s in
                subst_comp' uu____1976 comp in
              (uu____1969, uu____1973) in
            FStar_Syntax_Syntax.Tm_arrow uu____1961 in
          mk1 uu____1960
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___122_1997 = x in
            let uu____1998 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_1997.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_1997.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1998
            } in
          let phi1 =
            let uu____2004 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2004 phi in
=======
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
>>>>>>> origin/guido_tactics
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
<<<<<<< HEAD
                 (fun uu____2093  ->
                    match uu____2093 with
                    | (pat,wopt,branch) ->
                        let uu____2126 = subst_pat' s pat in
                        (match uu____2126 with
=======
                 (fun uu____1917  ->
                    match uu____1917 with
                    | (pat,wopt,branch) ->
                        let uu____1953 = subst_pat' s pat in
                        (match uu____1953 with
>>>>>>> origin/guido_tactics
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | None  -> None
                               | Some w ->
<<<<<<< HEAD
                                   let uu____2161 = subst' s1 w in
                                   Some uu____2161 in
=======
                                   let uu____1988 = subst' s1 w in
                                   Some uu____1988 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                      let uu____2226 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2226
=======
                      let uu____2051 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2051
>>>>>>> origin/guido_tactics
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
<<<<<<< HEAD
                            (let uu___123_2237 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___123_2237.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___123_2237.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___124_2239 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___124_2239.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___124_2239.FStar_Syntax_Syntax.lbeff);
=======
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
>>>>>>> origin/guido_tactics
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
<<<<<<< HEAD
          let uu____2258 =
            let uu____2259 =
              let uu____2264 = subst' s t0 in
              let uu____2267 =
                let uu____2268 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2268 in
              (uu____2264, uu____2267) in
            FStar_Syntax_Syntax.Tm_meta uu____2259 in
          mk1 uu____2258
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2310 =
            let uu____2311 =
              let uu____2316 = subst' s t0 in
              let uu____2319 =
                let uu____2320 =
                  let uu____2325 = subst' s t1 in (m, uu____2325) in
                FStar_Syntax_Syntax.Meta_monadic uu____2320 in
              (uu____2316, uu____2319) in
            FStar_Syntax_Syntax.Tm_meta uu____2311 in
          mk1 uu____2310
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____2344 =
            let uu____2345 =
              let uu____2350 = subst' s t0 in
              let uu____2353 =
                let uu____2354 =
                  let uu____2360 = subst' s t1 in (m1, m2, uu____2360) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____2354 in
              (uu____2350, uu____2353) in
            FStar_Syntax_Syntax.Tm_meta uu____2345 in
          mk1 uu____2344
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____2373 =
            let uu____2374 = let uu____2379 = subst' s t1 in (uu____2379, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2374 in
          mk1 uu____2373
=======
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
>>>>>>> origin/guido_tactics
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t2,s),memo) ->
        let t' = let uu____2442 = push_subst s t2 in compress uu____2442 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2449 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2453 -> compress t'
         | uu____2474 -> t')
=======
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____2264 = push_subst s t2 in compress uu____2264 in
        (FStar_Syntax_Unionfind.update_in_tx memo (Some t'); t')
    | uu____2271 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____2275 -> compress t'
         | uu____2290 -> t')
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
             (let uu___125_2499 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___125_2499.FStar_Range.use_range)
=======
             (let uu___135_2318 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___135_2318.FStar_Range.use_range)
>>>>>>> origin/guido_tactics
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  = fun s  -> fun t  -> subst_comp' ([s], None) t
<<<<<<< HEAD
let closing_subst bs =
  let uu____2527 =
    FStar_List.fold_right
      (fun uu____2542  ->
         fun uu____2543  ->
           match (uu____2542, uu____2543) with
           | ((x,uu____2558),(subst1,n1)) ->
               (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                 (n1 + (Prims.parse_int "1")))) bs
      ([], (Prims.parse_int "0")) in
  FStar_All.pipe_right uu____2527 FStar_Pervasives.fst
=======
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
>>>>>>> origin/guido_tactics
let open_binders' bs =
  let rec aux bs1 o =
    match bs1 with
    | [] -> ([], o)
    | (x,imp)::bs' ->
        let x' =
<<<<<<< HEAD
          let uu___126_2638 = FStar_Syntax_Syntax.freshen_bv x in
          let uu____2639 = subst o x.FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname =
              (uu___126_2638.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index =
              (uu___126_2638.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu____2639
          } in
        let o1 =
          let uu____2644 = shift_subst (Prims.parse_int "1") o in
          (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) :: uu____2644 in
        let uu____2646 = aux bs' o1 in
        (match uu____2646 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
=======
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
>>>>>>> origin/guido_tactics
  aux bs []
let open_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
<<<<<<< HEAD
  = fun bs  -> let uu____2678 = open_binders' bs in fst uu____2678
=======
  = fun bs  -> let uu____2487 = open_binders' bs in fst uu____2487
>>>>>>> origin/guido_tactics
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.subst_t)
  =
  fun bs  ->
    fun t  ->
<<<<<<< HEAD
      let uu____2698 = open_binders' bs in
      match uu____2698 with
      | (bs',opening) ->
          let uu____2718 = subst opening t in (bs', uu____2718, opening)
=======
      let uu____2509 = open_binders' bs in
      match uu____2509 with
      | (bs',opening) ->
          let uu____2529 = subst opening t in (bs', uu____2529, opening)
>>>>>>> origin/guido_tactics
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
<<<<<<< HEAD
      let uu____2731 = open_term' bs t in
      match uu____2731 with | (b,t1,uu____2739) -> (b, t1)
=======
      let uu____2544 = open_term' bs t in
      match uu____2544 with | (b,t1,uu____2552) -> (b, t1)
>>>>>>> origin/guido_tactics
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun t  ->
<<<<<<< HEAD
      let uu____2748 = open_binders' bs in
      match uu____2748 with
      | (bs',opening) ->
          let uu____2767 = subst_comp opening t in (bs', uu____2767)
=======
      let uu____2563 = open_binders' bs in
      match uu____2563 with
      | (bs',opening) ->
          let uu____2582 = subst_comp opening t in (bs', uu____2582)
>>>>>>> origin/guido_tactics
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.subst_t)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Pat_constant uu____2814 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____2830 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____2882  ->
                    fun uu____2883  ->
                      match (uu____2882, uu____2883) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____2960 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____2960 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____2830 with
           | (pats1,sub2,renaming1) ->
               ((let uu___127_3049 = p1 in
=======
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
>>>>>>> origin/guido_tactics
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
<<<<<<< HEAD
                   FStar_Syntax_Syntax.p =
                     (uu___127_3049.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___128_3060 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3061 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_3060.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_3060.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3061
            } in
          let sub2 =
            let uu____3066 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3066 in
          ((let uu___129_3074 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___129_3074.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___130_3080 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3081 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___130_3080.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___130_3080.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3081
            } in
          let sub2 =
            let uu____3086 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3086 in
          ((let uu___131_3094 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___131_3094.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___132_3105 = x in
            let uu____3106 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___132_3105.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___132_3105.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3106
            } in
          let t01 = subst sub1 t0 in
          ((let uu___133_3116 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___133_3116.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____3118 = open_pat_aux [] [] p in
    match uu____3118 with | (p1,sub1,uu____3133) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3148  ->
    match uu____3148 with
    | (p,wopt,e) ->
        let uu____3164 = open_pat p in
        (match uu____3164 with
=======
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
>>>>>>> origin/guido_tactics
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
<<<<<<< HEAD
                   let uu____3179 = subst opening w in Some uu____3179 in
=======
                   let uu____3032 = subst opening w in Some uu____3032 in
>>>>>>> origin/guido_tactics
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
<<<<<<< HEAD
    fun t  -> let uu____3188 = closing_subst bs in subst uu____3188 t
=======
    fun t  -> let uu____3043 = closing_subst bs in subst uu____3043 t
>>>>>>> origin/guido_tactics
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
<<<<<<< HEAD
    fun c  -> let uu____3196 = closing_subst bs in subst_comp uu____3196 c
=======
    fun c  -> let uu____3053 = closing_subst bs in subst_comp uu____3053 c
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            let uu___134_3229 = x in
            let uu____3230 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___134_3229.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___134_3229.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3230
            } in
          let s' =
            let uu____3235 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3235 in
          let uu____3237 = aux s' tl1 in (x1, imp) :: uu____3237 in
=======
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
>>>>>>> origin/guido_tactics
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
<<<<<<< HEAD
      let uu___135_3251 = lc in
      let uu____3252 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___135_3251.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3252;
        FStar_Syntax_Syntax.cflags =
          (uu___135_3251.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3257  ->
             let uu____3258 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____3258)
=======
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
>>>>>>> origin/guido_tactics
      }
let close_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t*
      FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Pat_constant uu____3287 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3300 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3338  ->
                    fun uu____3339  ->
                      match (uu____3338, uu____3339) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____3393 = aux sub2 p2 in
                          (match uu____3393 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____3300 with
           | (pats1,sub2) ->
               ((let uu___136_3447 = p1 in
=======
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
>>>>>>> origin/guido_tactics
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
<<<<<<< HEAD
                   FStar_Syntax_Syntax.p =
                     (uu___136_3447.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___137_3458 = x in
            let uu____3459 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___137_3458.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___137_3458.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3459
            } in
          let sub2 =
            let uu____3464 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3464 in
          ((let uu___138_3469 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___138_3469.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___139_3473 = x in
            let uu____3474 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___139_3473.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___139_3473.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3474
            } in
          let sub2 =
            let uu____3479 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____3479 in
          ((let uu___140_3484 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___140_3484.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___141_3493 = x in
            let uu____3494 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_3493.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_3493.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3494
            } in
          let t01 = subst sub1 t0 in
          ((let uu___142_3501 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___142_3501.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____3505  ->
    match uu____3505 with
    | (p,wopt,e) ->
        let uu____3521 = close_pat p in
        (match uu____3521 with
=======
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
>>>>>>> origin/guido_tactics
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | None  -> None
               | Some w ->
<<<<<<< HEAD
                   let uu____3542 = subst closing w in Some uu____3542 in
=======
                   let uu____3442 = subst closing w in Some uu____3442 in
>>>>>>> origin/guido_tactics
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list* FStar_Syntax_Syntax.univ_name
      Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
<<<<<<< HEAD
    let uu____3557 =
      let uu____3562 =
=======
    let uu____3462 =
      let uu____3467 =
>>>>>>> origin/guido_tactics
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  ->
                fun u  ->
                  let u' =
                    FStar_Syntax_Syntax.new_univ_name
                      (Some (u.FStar_Ident.idRange)) in
                  ((FStar_Syntax_Syntax.UN
                      ((n1 - i), (FStar_Syntax_Syntax.U_name u'))), u'))) in
<<<<<<< HEAD
      FStar_All.pipe_right uu____3562 FStar_List.unzip in
    match uu____3557 with | (s,us') -> (s, us')
let univ_var_closing:
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
=======
      FStar_All.pipe_right uu____3467 FStar_List.unzip in
    match uu____3462 with | (s,us') -> (s, us')
>>>>>>> origin/guido_tactics
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
  =
  fun us  ->
    fun t  ->
<<<<<<< HEAD
      let uu____3619 = univ_var_opening us in
      match uu____3619 with | (s,us') -> let t1 = subst s t in (us', t1)
=======
      let uu____3510 = univ_var_opening us in
      match uu____3510 with | (s,us') -> let t1 = subst s t in (us', t1)
>>>>>>> origin/guido_tactics
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
<<<<<<< HEAD
      let uu____3644 = univ_var_opening us in
      match uu____3644 with
      | (s,us') -> let uu____3657 = subst_comp s c in (us', uu____3657)
=======
      let uu____3537 = univ_var_opening us in
      match uu____3537 with
      | (s,us') -> let uu____3550 = subst_comp s c in (us', uu____3550)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____3695 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3695
      then (lbs, t)
      else
        (let uu____3701 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3719  ->
                  match uu____3719 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____3738 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____3738 in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___143_3742 = lb in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___143_3742.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___143_3742.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___143_3742.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___143_3742.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], []) in
         match uu____3701 with
=======
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
>>>>>>> origin/guido_tactics
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
<<<<<<< HEAD
                       let uu____3767 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3785  ->
                                match uu____3785 with
=======
                       let uu____3663 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3675  ->
                                match uu____3675 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                       match uu____3767 with
                       | (uu____3808,us,u_let_rec_opening) ->
                           let uu___144_3815 = lb in
                           let uu____3816 =
=======
                       match uu____3663 with
                       | (uu____3698,us,u_let_rec_opening) ->
                           let uu___154_3705 = lb in
                           let uu____3706 =
>>>>>>> origin/guido_tactics
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
<<<<<<< HEAD
                               (uu___144_3815.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___144_3815.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___144_3815.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3816
=======
                               (uu___154_3705.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___154_3705.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___154_3705.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3706
>>>>>>> origin/guido_tactics
                           })) in
             let t1 = subst let_rec_opening t in (lbs2, t1))
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list* FStar_Syntax_Syntax.term)
  =
  fun lbs  ->
    fun t  ->
<<<<<<< HEAD
      let uu____3832 = FStar_Syntax_Syntax.is_top_level lbs in
      if uu____3832
      then (lbs, t)
      else
        (let uu____3838 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____3851  ->
                  match uu____3851 with
                  | (i,out) ->
                      let uu____3862 =
                        let uu____3864 =
                          let uu____3865 =
                            let uu____3868 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                            (uu____3868, i) in
                          FStar_Syntax_Syntax.NM uu____3865 in
                        uu____3864 :: out in
                      ((i + (Prims.parse_int "1")), uu____3862)) lbs
             ((Prims.parse_int "0"), []) in
         match uu____3838 with
=======
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
>>>>>>> origin/guido_tactics
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
<<<<<<< HEAD
                       let uu____3889 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3901  ->
                                match uu____3901 with
=======
                       let uu____3770 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____3778  ->
                                match uu____3778 with
>>>>>>> origin/guido_tactics
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing) in
<<<<<<< HEAD
                       match uu____3889 with
                       | (uu____3914,u_let_rec_closing) ->
                           let uu___145_3918 = lb in
                           let uu____3919 =
=======
                       match uu____3770 with
                       | (uu____3791,u_let_rec_closing) ->
                           let uu___155_3795 = lb in
                           let uu____3796 =
>>>>>>> origin/guido_tactics
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname =
<<<<<<< HEAD
                               (uu___145_3918.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___145_3918.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___145_3918.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___145_3918.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3919
=======
                               (uu___155_3795.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_3795.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___155_3795.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_3795.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____3796
>>>>>>> origin/guido_tactics
                           })) in
             let t1 = subst let_rec_closing t in (lbs1, t1))
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun binders  ->
<<<<<<< HEAD
    fun uu____3929  ->
      match uu____3929 with
=======
    fun uu____3808  ->
      match uu____3808 with
>>>>>>> origin/guido_tactics
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
<<<<<<< HEAD
                 fun uu____3951  ->
                   match uu____3951 with
                   | (x,uu____3955) ->
=======
                 fun uu____3830  ->
                   match uu____3830 with
                   | (x,uu____3834) ->
>>>>>>> origin/guido_tactics
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term)
  =
  fun us  ->
<<<<<<< HEAD
    fun uu____3966  ->
      match uu____3966 with
=======
    fun uu____3850  ->
      match uu____3850 with
>>>>>>> origin/guido_tactics
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
<<<<<<< HEAD
          let uu____3986 = subst s t in (us', uu____3986)
=======
          let uu____3875 = subst s t in (us', uu____3875)
>>>>>>> origin/guido_tactics
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
<<<<<<< HEAD
            fun uu____4005  ->
              match uu____4005 with
              | (x,uu____4009) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____4027  ->
              match uu____4027 with
              | (x,uu____4031) -> FStar_Syntax_Syntax.NM (x, (n1 - i))))
=======
            fun uu____3894  ->
              match uu____3894 with
              | (x,uu____3898) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
>>>>>>> origin/guido_tactics
