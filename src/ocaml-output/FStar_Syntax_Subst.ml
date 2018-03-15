open Prims
let subst_to_string :
  'Auu____3 .
    (FStar_Syntax_Syntax.bv, 'Auu____3) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s ->
    let uu____20 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____38 ->
              match uu____38 with
              | (b, uu____44) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
    FStar_All.pipe_right uu____20 (FStar_String.concat ", ")
let rec apply_until_some :
  'Auu____53 'Auu____54 .
    ('Auu____53 -> 'Auu____54 FStar_Pervasives_Native.option) ->
      'Auu____53 Prims.list ->
        ('Auu____53 Prims.list, 'Auu____54) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____94 = f s0 in
          (match uu____94 with
           | FStar_Pervasives_Native.None -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry :
  'Auu____120 'Auu____121 'Auu____122 .
    ('Auu____120 -> 'Auu____121 -> 'Auu____122) ->
      'Auu____122 ->
        ('Auu____120, 'Auu____121) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____122
  =
  fun f ->
    fun x ->
      fun uu___34_146 ->
        match uu___34_146 with
        | FStar_Pervasives_Native.None -> x
        | FStar_Pervasives_Native.Some (a, b) -> f a b
let apply_until_some_then_map :
  'Auu____174 'Auu____175 'Auu____176 .
    ('Auu____174 -> 'Auu____175 FStar_Pervasives_Native.option) ->
      'Auu____174 Prims.list ->
        ('Auu____174 Prims.list -> 'Auu____175 -> 'Auu____176) ->
          'Auu____176 -> 'Auu____176
  =
  fun f ->
    fun s ->
      fun g ->
        fun t ->
          let uu____220 = apply_until_some f s in
          FStar_All.pipe_right uu____220 (map_some_curry g t)
let compose_subst :
  'Auu____243 'Auu____244 .
    ('Auu____243 Prims.list, 'Auu____244 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____243 Prims.list, 'Auu____244 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____243 Prims.list, 'Auu____244 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1 ->
    fun s2 ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____313 ->
            FStar_Pervasives_Native.snd s2
        | uu____318 -> FStar_Pervasives_Native.snd s1 in
      (s, ropt)
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,
      FStar_Range.range FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun t ->
    fun s ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____424 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv, uu____457) ->
        let uu____482 = FStar_Syntax_Unionfind.find uv in
        (match uu____482 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____492 =
               let uu____495 = force_uvar' t' in
               FStar_Pervasives_Native.fst uu____495 in
             (uu____492, true)
         | uu____506 -> (t, false))
    | uu____511 -> (t, false)
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____527 = force_uvar' t in
    match uu____527 with
    | (t', forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____555 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))) in
           (uu____555, forced))
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f, m) ->
        let uu____625 = FStar_ST.op_Bang m in
        (match uu____625 with
         | FStar_Pervasives_Native.None -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____694 = try_read_memo_aux t' in
             (match uu____694 with
              | (t'1, shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____768 -> (t, false)
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____780 = try_read_memo_aux t in
    FStar_Pervasives_Native.fst uu____780
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____801 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____801 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____805 -> u)
    | uu____808 -> u
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___35_825 ->
           match uu___35_825 with
           | FStar_Syntax_Syntax.DB (i, x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____830 =
                 let uu____831 =
                   let uu____832 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____832 in
                 FStar_Syntax_Syntax.bv_to_name uu____831 in
               FStar_Pervasives_Native.Some uu____830
           | uu____833 -> FStar_Pervasives_Native.None)
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___36_850 ->
           match uu___36_850 with
           | FStar_Syntax_Syntax.NM (x, i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____855 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___40_858 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___40_858.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___40_858.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____855
           | FStar_Syntax_Syntax.NT (x, t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____867 -> FStar_Pervasives_Native.None)
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___37_883 ->
           match uu___37_883 with
           | FStar_Syntax_Syntax.UN (y, t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____888 -> FStar_Pervasives_Native.None)
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___38_904 ->
           match uu___38_904 with
           | FStar_Syntax_Syntax.UD (y, i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____909 -> FStar_Pervasives_Native.None)
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s ->
    fun u ->
      let u1 = compress_univ u in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero -> u1
      | FStar_Syntax_Syntax.U_unknown -> u1
      | FStar_Syntax_Syntax.U_unif uu____931 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____941 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____941
      | FStar_Syntax_Syntax.U_max us ->
          let uu____945 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____945
let tag_with_range :
  'Auu____951 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____951, FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____982 = FStar_Range.use_range r in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____982 in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____985 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____985
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____987 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____987
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___41_993 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___41_993.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___42_995 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___42_995.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___42_995.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___43_997 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars = (uu___43_997.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range :
  'Auu____1003 .
    FStar_Ident.lident ->
      ('Auu____1003, FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1027 =
            let uu____1028 = FStar_Range.use_range r in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____1028 in
          FStar_Ident.set_lid_range l uu____1027
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r ->
    fun s ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1042 = FStar_Range.use_range r' in
          FStar_Range.set_use_range r uu____1042
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun t ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([], FStar_Pervasives_Native.None) -> t
      | ([]::[], FStar_Pervasives_Native.None) -> t
      | uu____1145 ->
          let t0 = try_read_memo t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1155 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1160 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1165 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t', s'), m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1274 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1275 =
                 let uu____1278 =
                   let uu____1279 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1279 in
                 FStar_Syntax_Syntax.mk uu____1278 in
               uu____1275 FStar_Pervasives_Native.None uu____1274
           | uu____1289 ->
               let uu____1290 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1290)
and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s ->
    fun flags ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___39_1304 ->
              match uu___39_1304 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1308 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1308
              | f -> f))
and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,
    FStar_Range.range FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s ->
    fun t ->
      match s with
      | ([], FStar_Pervasives_Native.None) -> t
      | ([]::[], FStar_Pervasives_Native.None) -> t
      | uu____1342 ->
          let uu___44_1353 = t in
          let uu____1354 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1361 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1366 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1369 =
            FStar_List.map
              (fun uu____1394 ->
                 match uu____1394 with
                 | (t1, imp) ->
                     let uu____1413 = subst' s t1 in (uu____1413, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1418 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1354;
            FStar_Syntax_Syntax.effect_name = uu____1361;
            FStar_Syntax_Syntax.result_typ = uu____1366;
            FStar_Syntax_Syntax.effect_args = uu____1369;
            FStar_Syntax_Syntax.flags = uu____1418
          }
and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,
    FStar_Range.range FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun t ->
      match s with
      | ([], FStar_Pervasives_Native.None) -> t
      | ([]::[], FStar_Pervasives_Native.None) -> t
      | uu____1455 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1, uopt) ->
               let uu____1478 = subst' s t1 in
               let uu____1479 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1478 uu____1479
           | FStar_Syntax_Syntax.GTotal (t1, uopt) ->
               let uu____1498 = subst' s t1 in
               let uu____1499 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1498 uu____1499
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1509 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1509)
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1 ->
    fun s ->
      match s with
      | FStar_Syntax_Syntax.DB (i, t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i, t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x, i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x, i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1524 -> s
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1 -> fun s -> FStar_List.map (shift n1) s
let shift_subst' :
  'Auu____1540 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list, 'Auu____1540)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list, 'Auu____1540)
          FStar_Pervasives_Native.tuple2
  =
  fun n1 ->
    fun s ->
      let uu____1567 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1567, (FStar_Pervasives_Native.snd s))
let subst_binder' :
  'Auu____1583 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv, 'Auu____1583) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.bv, 'Auu____1583) FStar_Pervasives_Native.tuple2
  =
  fun s ->
    fun uu____1599 ->
      match uu____1599 with
      | (x, imp) ->
          let uu____1606 =
            let uu___45_1607 = x in
            let uu____1608 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___45_1607.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___45_1607.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1608
            } in
          (uu____1606, imp)
let subst_binders' :
  'Auu____1614 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv, 'Auu____1614) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv, 'Auu____1614) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i ->
              fun b ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1674 = shift_subst' i s in
                   subst_binder' uu____1674 b)))
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  = fun s -> fun bs -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg' :
  'Auu____1700 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____1700)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____1700)
          FStar_Pervasives_Native.tuple2
  =
  fun s ->
    fun uu____1720 ->
      match uu____1720 with
      | (t, imp) -> let uu____1733 = subst' s t in (uu____1733, imp)
let subst_args' :
  'Auu____1740 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____1740)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____1740)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s -> FStar_List.map (subst_arg' s)
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list,
    FStar_Range.range FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat, Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun s ->
    fun p ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1828 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
            let uu____1849 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1903 ->
                      fun uu____1904 ->
                        match (uu____1903, uu____1904) with
                        | ((pats1, n2), (p2, imp)) ->
                            let uu____1983 = aux n2 p2 in
                            (match uu____1983 with
                             | (p3, m) -> (((p3, imp) :: pats1), m)))
                   ([], n1)) in
            (match uu____1849 with
             | (pats1, n2) ->
                 ((let uu___46_2041 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___46_2041.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___47_2067 = x in
              let uu____2068 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___47_2067.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___47_2067.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2068
              } in
            ((let uu___48_2074 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___48_2074.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___49_2090 = x in
              let uu____2091 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___49_2090.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___49_2090.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2091
              } in
            ((let uu___50_2097 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___50_2097.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___51_2118 = x in
              let uu____2119 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___51_2118.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___51_2118.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2119
              } in
            let t01 = subst' s1 t0 in
            ((let uu___52_2128 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___52_2128.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s ->
    fun lopt ->
      match lopt with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2148 =
            let uu___53_2149 = rc in
            let uu____2150 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___53_2149.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2150;
              FStar_Syntax_Syntax.residual_flags =
                (uu___53_2149.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2148
let (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun t ->
      let mk1 t' =
        let uu____2177 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2177 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2180 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2208 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2213 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2218 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2243 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2244 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2245 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2261 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2261 s
      | FStar_Syntax_Syntax.Tm_app (t0, args) ->
          let uu____2290 =
            let uu____2291 =
              let uu____2306 = subst' s t0 in
              let uu____2309 = subst_args' s args in (uu____2306, uu____2309) in
            FStar_Syntax_Syntax.Tm_app uu____2291 in
          mk1 uu____2290
      | FStar_Syntax_Syntax.Tm_ascribed (t0, (annot, topt), lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2404 = subst' s t1 in FStar_Util.Inl uu____2404
            | FStar_Util.Inr c ->
                let uu____2418 = subst_comp' s c in FStar_Util.Inr uu____2418 in
          let uu____2425 =
            let uu____2426 =
              let uu____2453 = subst' s t0 in
              let uu____2456 =
                let uu____2473 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2473) in
              (uu____2453, uu____2456, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2426 in
          mk1 uu____2425
      | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2557 =
            let uu____2558 =
              let uu____2575 = subst_binders' s bs in
              let uu____2582 = subst' s' body in
              let uu____2585 = push_subst_lcomp s' lopt in
              (uu____2575, uu____2582, uu____2585) in
            FStar_Syntax_Syntax.Tm_abs uu____2558 in
          mk1 uu____2557
      | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
          let n1 = FStar_List.length bs in
          let uu____2621 =
            let uu____2622 =
              let uu____2635 = subst_binders' s bs in
              let uu____2642 =
                let uu____2645 = shift_subst' n1 s in
                subst_comp' uu____2645 comp in
              (uu____2635, uu____2642) in
            FStar_Syntax_Syntax.Tm_arrow uu____2622 in
          mk1 uu____2621
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let x1 =
            let uu___54_2677 = x in
            let uu____2678 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___54_2677.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___54_2677.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2678
            } in
          let phi1 =
            let uu____2684 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2684 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0, pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2811 ->
                    match uu____2811 with
                    | (pat, wopt, branch) ->
                        let uu____2857 = subst_pat' s pat in
                        (match uu____2857 with
                         | (pat1, n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2905 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2905 in
                             let branch1 = subst' s1 branch in
                             (pat1, wopt1, branch1)))) in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) ->
          let n1 = FStar_List.length lbs in
          let sn = shift_subst' n1 s in
          let body1 = subst' sn body in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp in
                    let lbd =
                      let uu____2990 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2990
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___55_3005 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___55_3005.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___55_3005.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___56_3007 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___56_3007.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___56_3007.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___56_3007.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___56_3007.FStar_Syntax_Syntax.lbpos)
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3034 =
            let uu____3035 =
              let uu____3042 = subst' s t0 in
              let uu____3045 =
                let uu____3046 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____3046 in
              (uu____3042, uu____3045) in
            FStar_Syntax_Syntax.Tm_meta uu____3035 in
          mk1 uu____3034
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic (m, t1)) ->
          let uu____3106 =
            let uu____3107 =
              let uu____3114 = subst' s t0 in
              let uu____3117 =
                let uu____3118 =
                  let uu____3125 = subst' s t1 in (m, uu____3125) in
                FStar_Syntax_Syntax.Meta_monadic uu____3118 in
              (uu____3114, uu____3117) in
            FStar_Syntax_Syntax.Tm_meta uu____3107 in
          mk1 uu____3106
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t1)) ->
          let uu____3144 =
            let uu____3145 =
              let uu____3152 = subst' s t0 in
              let uu____3155 =
                let uu____3156 =
                  let uu____3165 = subst' s t1 in (m1, m2, uu____3165) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3156 in
              (uu____3152, uu____3155) in
            FStar_Syntax_Syntax.Tm_meta uu____3145 in
          mk1 uu____3144
      | FStar_Syntax_Syntax.Tm_meta
          (t0, FStar_Syntax_Syntax.Meta_quoted (t1, qi)) ->
          if qi.FStar_Syntax_Syntax.qopen
          then
            let uu____3185 =
              let uu____3186 =
                let uu____3193 = subst' s t0 in
                let uu____3196 =
                  let uu____3197 =
                    let uu____3204 = subst' s t1 in (uu____3204, qi) in
                  FStar_Syntax_Syntax.Meta_quoted uu____3197 in
                (uu____3193, uu____3196) in
              FStar_Syntax_Syntax.Tm_meta uu____3186 in
            mk1 uu____3185
          else
            (let uu____3212 =
               let uu____3213 =
                 let uu____3220 = subst' s t0 in
                 (uu____3220, (FStar_Syntax_Syntax.Meta_quoted (t1, qi))) in
               FStar_Syntax_Syntax.Tm_meta uu____3213 in
             mk1 uu____3212)
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let uu____3233 =
            let uu____3234 = let uu____3241 = subst' s t1 in (uu____3241, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3234 in
          mk1 uu____3233
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = try_read_memo t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t', s), memo) ->
        ((let uu____3304 =
            let uu____3309 = push_subst s t' in
            FStar_Pervasives_Native.Some uu____3309 in
          FStar_ST.op_Colon_Equals memo uu____3304);
         compress t1)
    | uu____3363 ->
        let uu____3364 = force_uvar t1 in
        (match uu____3364 with
         | (t', forced) ->
             (match t'.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3377 -> compress t'
              | uu____3402 -> t'))
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun t -> subst' ([s], FStar_Pervasives_Native.None) t
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r ->
    fun t ->
      let uu____3429 =
        let uu____3430 =
          let uu____3433 =
            let uu____3434 = FStar_Range.use_range r in
            FStar_Range.set_def_range r uu____3434 in
          FStar_Pervasives_Native.Some uu____3433 in
        ([], uu____3430) in
      subst' uu____3429 t
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s -> fun t -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs ->
    let uu____3468 =
      FStar_List.fold_right
        (fun uu____3491 ->
           fun uu____3492 ->
             match (uu____3491, uu____3492) with
             | ((x, uu____3520), (subst1, n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3468 FStar_Pervasives_Native.fst
let open_binders' :
  'Auu____3553 .
    (FStar_Syntax_Syntax.bv, 'Auu____3553) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv, 'Auu____3553) FStar_Pervasives_Native.tuple2
         Prims.list,
        FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x, imp)::bs' ->
          let x' =
            let uu___57_3659 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3660 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___57_3659.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___57_3659.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3660
            } in
          let o1 =
            let uu____3666 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3666 in
          let uu____3669 = aux bs' o1 in
          (match uu____3669 with | (bs'1, o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____3727 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3727
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.subst_t) FStar_Pervasives_Native.tuple3)
  =
  fun bs ->
    fun t ->
      let uu____3760 = open_binders' bs in
      match uu____3760 with
      | (bs', opening) ->
          let uu____3797 = subst opening t in (bs', uu____3797, opening)
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs ->
    fun t ->
      let uu____3816 = open_term' bs t in
      match uu____3816 with | (b, t1, uu____3829) -> (b, t1)
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs ->
    fun t ->
      let uu____3840 = open_binders' bs in
      match uu____3840 with
      | (bs', opening) ->
          let uu____3875 = subst_comp opening t in (bs', uu____3875)
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat, FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3955 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu____3984 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4076 ->
                    fun uu____4077 ->
                      match (uu____4076, uu____4077) with
                      | ((pats1, sub2, renaming1), (p2, imp)) ->
                          let uu____4225 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4225 with
                           | (p3, sub3, renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3984 with
           | (pats1, sub2, renaming1) ->
               ((let uu___58_4395 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___58_4395.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___59_4414 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4415 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___59_4414.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___59_4414.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4415
            } in
          let sub2 =
            let uu____4421 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4421 in
          ((let uu___60_4435 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___60_4435.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___61_4444 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4445 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___61_4444.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___61_4444.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4445
            } in
          let sub2 =
            let uu____4451 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4451 in
          ((let uu___62_4465 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___62_4465.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___63_4479 = x in
            let uu____4480 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___63_4479.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___63_4479.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4480
            } in
          let t01 = subst sub1 t0 in
          ((let uu___64_4495 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___64_4495.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4498 = open_pat_aux [] [] p in
    match uu____4498 with | (p1, sub1, uu____4525) -> (p1, sub1)
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____4552 ->
    match uu____4552 with
    | (p, wopt, e) ->
        let uu____4572 = open_pat p in
        (match uu____4572 with
         | (p1, opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4591 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4591 in
             let e1 = subst opening e in (p1, wopt1, e1))
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs -> fun t -> let uu____4601 = closing_subst bs in subst uu____4601 t
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs ->
    fun c -> let uu____4610 = closing_subst bs in subst_comp uu____4610 c
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x, imp)::tl1 ->
          let x1 =
            let uu___65_4661 = x in
            let uu____4662 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___65_4661.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___65_4661.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4662
            } in
          let s' =
            let uu____4668 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4668 in
          let uu____4671 = aux s' tl1 in (x1, imp) :: uu____4671 in
    aux [] bs
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs ->
    fun lc ->
      let s = closing_subst bs in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4693 ->
           let uu____4694 = FStar_Syntax_Syntax.lcomp_comp lc in
           subst_comp s uu____4694)
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,
      FStar_Syntax_Syntax.subst_elt Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4741 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let uu____4764 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4830 ->
                    fun uu____4831 ->
                      match (uu____4830, uu____4831) with
                      | ((pats1, sub2), (p2, imp)) ->
                          let uu____4934 = aux sub2 p2 in
                          (match uu____4934 with
                           | (p3, sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4764 with
           | (pats1, sub2) ->
               ((let uu___66_5036 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___66_5036.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___67_5055 = x in
            let uu____5056 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___67_5055.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___67_5055.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5056
            } in
          let sub2 =
            let uu____5062 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5062 in
          ((let uu___68_5070 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___68_5070.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___69_5075 = x in
            let uu____5076 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___69_5075.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___69_5075.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5076
            } in
          let sub2 =
            let uu____5082 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5082 in
          ((let uu___70_5090 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___70_5090.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
          let x1 =
            let uu___71_5100 = x in
            let uu____5101 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___71_5100.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___71_5100.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5101
            } in
          let t01 = subst sub1 t0 in
          ((let uu___72_5110 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___72_5110.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5115 ->
    match uu____5115 with
    | (p, wopt, e) ->
        let uu____5135 = close_pat p in
        (match uu____5135 with
         | (p1, closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5166 = subst closing w in
                   FStar_Pervasives_Native.Some uu____5166 in
             let e1 = subst closing e in (p1, wopt1, e1))
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,
      FStar_Syntax_Syntax.univ_name Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun us ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i ->
              fun u ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u)))) in
    (s, us)
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i -> fun u -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun us ->
    fun t ->
      let uu____5221 = univ_var_opening us in
      match uu____5221 with | (s, us') -> let t1 = subst s t in (us', t1)
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us ->
    fun c ->
      let uu____5261 = univ_var_opening us in
      match uu____5261 with
      | (s, us') -> let uu____5284 = subst_comp s c in (us', uu____5284)
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us -> fun t -> let s = univ_var_closing us in subst s t
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us ->
    fun c ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i -> fun u -> FStar_Syntax_Syntax.UD (u, (n1 - i)))) in
      subst_comp s c
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs ->
    fun t ->
      let uu____5328 =
        let uu____5339 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5339
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu____5372 ->
                 match uu____5372 with
                 | (i, lbs1, out) ->
                     let x =
                       let uu____5405 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5405 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___73_5411 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___73_5411.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___73_5411.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___73_5411.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___73_5411.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___73_5411.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___73_5411.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____5328 with
      | (n_let_recs, lbs1, let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb ->
                    let uu____5449 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu____5477 ->
                             match uu____5477 with
                             | (i, us, out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5449 with
                    | (uu____5518, us, u_let_rec_opening) ->
                        let uu___74_5529 = lb in
                        let uu____5530 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5533 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___74_5529.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5530;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___74_5529.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5533;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___74_5529.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___74_5529.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs ->
    fun t ->
      let uu____5555 =
        let uu____5562 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5562
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb ->
               fun uu____5584 ->
                 match uu____5584 with
                 | (i, out) ->
                     let uu____5603 =
                       let uu____5606 =
                         let uu____5607 =
                           let uu____5612 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5612, i) in
                         FStar_Syntax_Syntax.NM uu____5607 in
                       uu____5606 :: out in
                     ((i + (Prims.parse_int "1")), uu____5603)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____5555 with
      | (n_let_recs, let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____5644 =
                      FStar_List.fold_right
                        (fun u ->
                           fun uu____5662 ->
                             match uu____5662 with
                             | (i, out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5644 with
                    | (uu____5685, u_let_rec_closing) ->
                        let uu___75_5691 = lb in
                        let uu____5692 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5695 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___75_5691.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___75_5691.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5692;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___75_5691.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5695;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___75_5691.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___75_5691.FStar_Syntax_Syntax.lbpos)
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders ->
    fun uu____5706 ->
      match uu____5706 with
      | (us, t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i ->
                 fun uu____5731 ->
                   match uu____5731 with
                   | (x, uu____5737) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us ->
    fun uu____5752 ->
      match uu____5752 with
      | (us', t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i -> fun x -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5774 = subst s t in (us', uu____5774)
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s ->
    fun uu____5784 ->
      match uu____5784 with
      | (us, t) ->
          let s1 = shift_subst (FStar_List.length us) s in
          let uu____5794 = subst s1 t in (us, uu____5794)
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i ->
            fun uu____5816 ->
              match uu____5816 with
              | (x, uu____5822) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs -> closing_subst bs