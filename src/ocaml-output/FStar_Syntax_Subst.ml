open Prims
let subst_to_string:
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____22 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____40  ->
              match uu____40 with
              | (b,uu____46) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
    FStar_All.pipe_right uu____22 (FStar_String.concat ", ")
let rec apply_until_some:
  'Auu____57 'Auu____58 .
    ('Auu____58 -> 'Auu____57 FStar_Pervasives_Native.option) ->
      'Auu____58 Prims.list ->
        ('Auu____58 Prims.list,'Auu____57) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____98 = f s0 in
          (match uu____98 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry:
  'Auu____130 'Auu____131 'Auu____132 .
    ('Auu____132 -> 'Auu____131 -> 'Auu____130) ->
      'Auu____130 ->
        ('Auu____132,'Auu____131) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____130
  =
  fun f  ->
    fun x  ->
      fun uu___103_156  ->
        match uu___103_156 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map:
  'Auu____191 'Auu____192 'Auu____193 .
    ('Auu____193 -> 'Auu____192 FStar_Pervasives_Native.option) ->
      'Auu____193 Prims.list ->
        ('Auu____193 Prims.list -> 'Auu____192 -> 'Auu____191) ->
          'Auu____191 -> 'Auu____191
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____237 = apply_until_some f s in
          FStar_All.pipe_right uu____237 (map_some_curry g t)
let compose_subst:
  'Auu____264 'Auu____265 .
    ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____334 ->
            FStar_Pervasives_Native.snd s2
        | uu____339 -> FStar_Pervasives_Native.snd s1 in
      (s, ropt)
let delay:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____447 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec force_uvar':
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____473) ->
        let uu____498 = FStar_Syntax_Unionfind.find uv in
        (match uu____498 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____504 -> t)
    | uu____507 -> t
let force_uvar:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let t' = force_uvar' t in
    let uu____525 = FStar_Util.physical_equality t t' in
    if uu____525
    then (t, false)
    else
      (let uu____537 =
         delay t'
           ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))) in
       (uu____537, true))
let rec force_delayed_thunk:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____600 = FStar_ST.op_Bang m in
        (match uu____600 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____700 -> t
let rec compress_univ:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____714 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____714 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____718 -> u)
    | uu____721 -> u
let subst_bv:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_740  ->
           match uu___104_740 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____745 =
                 let uu____746 =
                   let uu____747 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____747 in
                 FStar_Syntax_Syntax.bv_to_name uu____746 in
               FStar_Pervasives_Native.Some uu____745
           | uu____748 -> FStar_Pervasives_Native.None)
let subst_nm:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_767  ->
           match uu___105_767 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____772 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_775 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_775.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_775.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____772
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____784 -> FStar_Pervasives_Native.None)
let subst_univ_bv:
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_802  ->
           match uu___106_802 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____807 -> FStar_Pervasives_Native.None)
let subst_univ_nm:
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___107_825  ->
           match uu___107_825 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____830 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.U_unif uu____854 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____864 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____864
      | FStar_Syntax_Syntax.U_max us ->
          let uu____868 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____868
let tag_with_range:
  'Auu____877 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____877,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____910 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____910
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____912 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____912
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___110_918 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___110_918.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___111_920 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___111_920.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___111_920.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___112_922 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___112_922.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range:
  'Auu____931 .
    FStar_Ident.lident ->
      ('Auu____931,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____955 =
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
          FStar_Ident.set_lid_range l uu____955
let mk_range:
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' -> FStar_Range.set_use_range r r'
let rec subst':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1073 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1083 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1088 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1093 ->
               let uu____1110 = force_uvar t in
               (match uu____1110 with
                | (t1,b) -> if b then subst' s t1 else tag_with_range t0 s)
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1220 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1221 =
                 let uu____1224 =
                   let uu____1225 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1225 in
                 FStar_Syntax_Syntax.mk uu____1224 in
               uu____1221 FStar_Pervasives_Native.None uu____1220
           | uu____1235 ->
               let uu____1236 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1236)
and subst_flags':
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___108_1250  ->
              match uu___108_1250 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1254 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1254
              | f -> f))
and subst_comp_typ':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1288 ->
          let uu___113_1299 = t in
          let uu____1300 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1307 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1312 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1315 =
            FStar_List.map
              (fun uu____1340  ->
                 match uu____1340 with
                 | (t1,imp) ->
                     let uu____1359 = subst' s t1 in (uu____1359, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1364 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1300;
            FStar_Syntax_Syntax.effect_name = uu____1307;
            FStar_Syntax_Syntax.result_typ = uu____1312;
            FStar_Syntax_Syntax.effect_args = uu____1315;
            FStar_Syntax_Syntax.flags = uu____1364
          }
and subst_comp':
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1401 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1424 = subst' s t1 in
               let uu____1425 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1424 uu____1425
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1444 = subst' s t1 in
               let uu____1445 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1444 uu____1445
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1455 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1455)
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
      | FStar_Syntax_Syntax.NT uu____1472 -> s
let shift_subst:
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst':
  'Auu____1493 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1493)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1493)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1520 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1520, (FStar_Pervasives_Native.snd s))
let subst_binder':
  'Auu____1539 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1539) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1539) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1555  ->
      match uu____1555 with
      | (x,imp) ->
          let uu____1562 =
            let uu___114_1563 = x in
            let uu____1564 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___114_1563.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___114_1563.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1564
            } in
          (uu____1562, imp)
let subst_binders':
  'Auu____1573 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1573) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1573) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1633 = shift_subst' i s in
                   subst_binder' uu____1633 b)))
let subst_binders:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg':
  'Auu____1664 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1664)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1664)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1684  ->
      match uu____1684 with
      | (t,imp) -> let uu____1697 = subst' s t in (uu____1697, imp)
let subst_args':
  'Auu____1707 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1707)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1707)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s)
let subst_pat':
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1797 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1818 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1872  ->
                      fun uu____1873  ->
                        match (uu____1872, uu____1873) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1952 = aux n2 p2 in
                            (match uu____1952 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1818 with
             | (pats1,n2) ->
                 ((let uu___115_2010 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___115_2010.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_2036 = x in
              let uu____2037 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_2036.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_2036.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2037
              } in
            ((let uu___117_2043 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___117_2043.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___118_2059 = x in
              let uu____2060 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___118_2059.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___118_2059.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2060
              } in
            ((let uu___119_2066 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___119_2066.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___120_2087 = x in
              let uu____2088 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_2087.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_2087.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2088
              } in
            let t01 = subst' s1 t0 in
            ((let uu___121_2097 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___121_2097.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let push_subst_lcomp:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2119 =
            let uu___122_2120 = rc in
            let uu____2121 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___122_2120.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2121;
              FStar_Syntax_Syntax.residual_flags =
                (uu___122_2120.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2119
let push_subst:
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2150 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2150 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2153 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2180 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2185 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2194 ->
          let uu____2211 = force_uvar t in
          (match uu____2211 with
           | (t',b) -> if b then subst' s t' else tag_with_range t s)
      | FStar_Syntax_Syntax.Tm_type uu____2233 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2234 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2235 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2251 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2251 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2280 =
            let uu____2281 =
              let uu____2296 = subst' s t0 in
              let uu____2299 = subst_args' s args in (uu____2296, uu____2299) in
            FStar_Syntax_Syntax.Tm_app uu____2281 in
          mk1 uu____2280
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2394 = subst' s t1 in FStar_Util.Inl uu____2394
            | FStar_Util.Inr c ->
                let uu____2408 = subst_comp' s c in FStar_Util.Inr uu____2408 in
          let uu____2415 =
            let uu____2416 =
              let uu____2443 = subst' s t0 in
              let uu____2446 =
                let uu____2463 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2463) in
              (uu____2443, uu____2446, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2416 in
          mk1 uu____2415
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2547 =
            let uu____2548 =
              let uu____2565 = subst_binders' s bs in
              let uu____2572 = subst' s' body in
              let uu____2575 = push_subst_lcomp s' lopt in
              (uu____2565, uu____2572, uu____2575) in
            FStar_Syntax_Syntax.Tm_abs uu____2548 in
          mk1 uu____2547
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2611 =
            let uu____2612 =
              let uu____2625 = subst_binders' s bs in
              let uu____2632 =
                let uu____2635 = shift_subst' n1 s in
                subst_comp' uu____2635 comp in
              (uu____2625, uu____2632) in
            FStar_Syntax_Syntax.Tm_arrow uu____2612 in
          mk1 uu____2611
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___123_2667 = x in
            let uu____2668 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_2667.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_2667.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2668
            } in
          let phi1 =
            let uu____2674 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2674 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2801  ->
                    match uu____2801 with
                    | (pat,wopt,branch) ->
                        let uu____2847 = subst_pat' s pat in
                        (match uu____2847 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2895 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2895 in
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
                      let uu____2980 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2980
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___124_2995 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_2995.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_2995.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___125_2997 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_2997.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_2997.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3024 =
            let uu____3025 =
              let uu____3032 = subst' s t0 in
              let uu____3035 =
                let uu____3036 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____3036 in
              (uu____3032, uu____3035) in
            FStar_Syntax_Syntax.Tm_meta uu____3025 in
          mk1 uu____3024
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3096 =
            let uu____3097 =
              let uu____3104 = subst' s t0 in
              let uu____3107 =
                let uu____3108 =
                  let uu____3115 = subst' s t1 in (m, uu____3115) in
                FStar_Syntax_Syntax.Meta_monadic uu____3108 in
              (uu____3104, uu____3107) in
            FStar_Syntax_Syntax.Tm_meta uu____3097 in
          mk1 uu____3096
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3134 =
            let uu____3135 =
              let uu____3142 = subst' s t0 in
              let uu____3145 =
                let uu____3146 =
                  let uu____3155 = subst' s t1 in (m1, m2, uu____3155) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3146 in
              (uu____3142, uu____3145) in
            FStar_Syntax_Syntax.Tm_meta uu____3135 in
          mk1 uu____3134
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3168 =
            let uu____3169 = let uu____3176 = subst' s t1 in (uu____3176, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3169 in
          mk1 uu____3168
let rec compress: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3240 = push_subst s t2 in compress uu____3240 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3260 ->
        let uu____3261 = force_uvar t1 in
        (match uu____3261 with
         | (t',uu____3269) ->
             (match t'.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3274 -> compress t'
              | uu____3299 -> t'))
let subst:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let set_use_range:
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      subst'
        ([],
          (FStar_Pervasives_Native.Some
             (let uu___126_3339 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___126_3339.FStar_Range.use_range)
              }))) t
let subst_comp:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let closing_subst:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3368 =
      FStar_List.fold_right
        (fun uu____3391  ->
           fun uu____3392  ->
             match (uu____3391, uu____3392) with
             | ((x,uu____3420),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3368 FStar_Pervasives_Native.fst
let open_binders':
  'Auu____3455 .
    (FStar_Syntax_Syntax.bv,'Auu____3455) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3455) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___127_3561 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3562 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_3561.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_3561.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3562
            } in
          let o1 =
            let uu____3568 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3568 in
          let uu____3571 = aux bs' o1 in
          (match uu____3571 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let open_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3630 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3630
let open_term':
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3665 = open_binders' bs in
      match uu____3665 with
      | (bs',opening) ->
          let uu____3702 = subst opening t in (bs', uu____3702, opening)
let open_term:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3723 = open_term' bs t in
      match uu____3723 with | (b,t1,uu____3736) -> (b, t1)
let open_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3749 = open_binders' bs in
      match uu____3749 with
      | (bs',opening) ->
          let uu____3784 = subst_comp opening t in (bs', uu____3784)
let open_pat:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3865 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3894 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3986  ->
                    fun uu____3987  ->
                      match (uu____3986, uu____3987) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4135 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4135 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3894 with
           | (pats1,sub2,renaming1) ->
               ((let uu___128_4305 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_4305.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___129_4324 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4325 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_4324.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_4324.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4325
            } in
          let sub2 =
            let uu____4331 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4331 in
          ((let uu___130_4345 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___130_4345.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___131_4354 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4355 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_4354.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_4354.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4355
            } in
          let sub2 =
            let uu____4361 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4361 in
          ((let uu___132_4375 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___132_4375.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_4389 = x in
            let uu____4390 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_4389.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_4389.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4390
            } in
          let t01 = subst sub1 t0 in
          ((let uu___134_4405 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_4405.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4408 = open_pat_aux [] [] p in
    match uu____4408 with | (p1,sub1,uu____4435) -> (p1, sub1)
let open_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4463  ->
    match uu____4463 with
    | (p,wopt,e) ->
        let uu____4483 = open_pat p in
        (match uu____4483 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4502 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4502 in
             let e1 = subst opening e in (p1, wopt1, e1))
let close:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4514 = closing_subst bs in subst uu____4514 t
let close_comp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4525 = closing_subst bs in subst_comp uu____4525 c
let close_binders: FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___135_4577 = x in
            let uu____4578 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_4577.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_4577.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4578
            } in
          let s' =
            let uu____4584 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4584 in
          let uu____4587 = aux s' tl1 in (x1, imp) :: uu____4587 in
    aux [] bs
let close_lcomp:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___136_4609 = lc in
      let uu____4610 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___136_4609.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4610;
        FStar_Syntax_Syntax.cflags =
          (uu___136_4609.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4615  ->
             let uu____4616 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____4616)
      }
let close_pat:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4664 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4687 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4753  ->
                    fun uu____4754  ->
                      match (uu____4753, uu____4754) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4857 = aux sub2 p2 in
                          (match uu____4857 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4687 with
           | (pats1,sub2) ->
               ((let uu___137_4959 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___137_4959.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___138_4978 = x in
            let uu____4979 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_4978.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_4978.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4979
            } in
          let sub2 =
            let uu____4985 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4985 in
          ((let uu___139_4993 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___139_4993.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___140_4998 = x in
            let uu____4999 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_4998.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_4998.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4999
            } in
          let sub2 =
            let uu____5005 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5005 in
          ((let uu___141_5013 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___141_5013.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_5023 = x in
            let uu____5024 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_5023.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_5023.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5024
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_5033 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___143_5033.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let close_branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____5039  ->
    match uu____5039 with
    | (p,wopt,e) ->
        let uu____5059 = close_pat p in
        (match uu____5059 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5090 = subst closing w in
                   FStar_Pervasives_Native.Some uu____5090 in
             let e1 = subst closing e in (p1, wopt1, e1))
let univ_var_opening:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u)))) in
    (s, us)
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
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun t  ->
      let uu____5149 = univ_var_opening us in
      match uu____5149 with | (s,us') -> let t1 = subst s t in (us', t1)
let open_univ_vars_comp:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5191 = univ_var_opening us in
      match uu____5191 with
      | (s,us') -> let uu____5214 = subst_comp s c in (us', uu____5214)
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
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5264 =
        let uu____5275 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5275
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5308  ->
                 match uu____5308 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5341 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5341 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___144_5347 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___144_5347.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___144_5347.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___144_5347.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___144_5347.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____5264 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5385 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5413  ->
                             match uu____5413 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5385 with
                    | (uu____5454,us,u_let_rec_opening) ->
                        let uu___145_5465 = lb in
                        let uu____5466 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5469 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___145_5465.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5466;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___145_5465.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5469
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let close_let_rec:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5493 =
        let uu____5500 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5500
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5522  ->
                 match uu____5522 with
                 | (i,out) ->
                     let uu____5541 =
                       let uu____5544 =
                         let uu____5545 =
                           let uu____5550 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5550, i) in
                         FStar_Syntax_Syntax.NM uu____5545 in
                       uu____5544 :: out in
                     ((i + (Prims.parse_int "1")), uu____5541)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____5493 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5582 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5600  ->
                             match uu____5600 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5582 with
                    | (uu____5623,u_let_rec_closing) ->
                        let uu___146_5629 = lb in
                        let uu____5630 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5633 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___146_5629.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___146_5629.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5630;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___146_5629.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5633
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let close_tscheme:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5646  ->
      match uu____5646 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5671  ->
                   match uu____5671 with
                   | (x,uu____5677) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let close_univ_vars_tscheme:
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5694  ->
      match uu____5694 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5716 = subst s t in (us', uu____5716)
let opening_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5739  ->
              match uu____5739 with
              | (x,uu____5745) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let closing_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs