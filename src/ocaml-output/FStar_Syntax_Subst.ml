open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string=
  fun s  ->
    let uu____22 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____40  ->
              match uu____40 with
              | (b,uu____46) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)) in
    FStar_All.pipe_right uu____22 (FStar_String.concat ", ")
let rec apply_until_some :
  'Auu____59 'Auu____60 .
    ('Auu____60 -> 'Auu____59 FStar_Pervasives_Native.option) ->
      'Auu____60 Prims.list ->
        ('Auu____60 Prims.list,'Auu____59) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option=
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____100 = f s0 in
          (match uu____100 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
let map_some_curry :
  'Auu____132 'Auu____133 'Auu____134 .
    ('Auu____134 -> 'Auu____133 -> 'Auu____132) ->
      'Auu____132 ->
        ('Auu____134,'Auu____133) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____132=
  fun f  ->
    fun x  ->
      fun uu___103_158  ->
        match uu___103_158 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
let apply_until_some_then_map :
  'Auu____193 'Auu____194 'Auu____195 .
    ('Auu____195 -> 'Auu____194 FStar_Pervasives_Native.option) ->
      'Auu____195 Prims.list ->
        ('Auu____195 Prims.list -> 'Auu____194 -> 'Auu____193) ->
          'Auu____193 -> 'Auu____193=
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____239 = apply_until_some f s in
          FStar_All.pipe_right uu____239 (map_some_curry g t)
let compose_subst :
  'Auu____266 'Auu____267 .
    ('Auu____267 Prims.list,'Auu____266 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____267 Prims.list,'Auu____266 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____267 Prims.list,'Auu____266 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2=
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2) in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____336 ->
            FStar_Pervasives_Native.snd s2
        | uu____341 -> FStar_Pervasives_Native.snd s1 in
      (s, ropt)
let (delay
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                            FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)=
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____449 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
let rec (force_uvar'
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____475) ->
        let uu____500 = FStar_Syntax_Unionfind.find uv in
        (match uu____500 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____506 -> t)
    | uu____509 -> t
let (force_uvar
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun t  ->
    let t' = force_uvar' t in
    let uu____523 = FStar_Util.physical_equality t t' in
    if uu____523
    then t
    else
      delay t'
        ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
let rec (force_delayed_thunk
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____591 = FStar_ST.op_Bang m in
        (match uu____591 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t' in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____691 -> t
let rec (compress_univ
  :FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)=
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____705 = FStar_Syntax_Unionfind.univ_find u' in
        (match uu____705 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____709 -> u)
    | uu____712 -> u
let (subst_bv
  :FStar_Syntax_Syntax.bv ->
     FStar_Syntax_Syntax.subst_elt Prims.list ->
       FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)=
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_731  ->
           match uu___104_731 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____736 =
                 let uu____737 =
                   let uu____738 = FStar_Syntax_Syntax.range_of_bv a in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____738 in
                 FStar_Syntax_Syntax.bv_to_name uu____737 in
               FStar_Pervasives_Native.Some uu____736
           | uu____739 -> FStar_Pervasives_Native.None)
let (subst_nm
  :FStar_Syntax_Syntax.bv ->
     FStar_Syntax_Syntax.subst_elt Prims.list ->
       FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)=
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_758  ->
           match uu___105_758 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____763 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_766 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_766.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_766.FStar_Syntax_Syntax.sort)
                    }) in
               FStar_Pervasives_Native.Some uu____763
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____775 -> FStar_Pervasives_Native.None)
let (subst_univ_bv
  :Prims.int ->
     FStar_Syntax_Syntax.subst_elt Prims.list ->
       FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)=
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_793  ->
           match uu___106_793 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____798 -> FStar_Pervasives_Native.None)
let (subst_univ_nm
  :FStar_Syntax_Syntax.univ_name ->
     FStar_Syntax_Syntax.subst_elt Prims.list ->
       FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)=
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___107_816  ->
           match uu___107_816 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____821 -> FStar_Pervasives_Native.None)
let rec (subst_univ
  :FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
     FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)=
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
      | FStar_Syntax_Syntax.U_unif uu____845 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____855 = subst_univ s u2 in
          FStar_Syntax_Syntax.U_succ uu____855
      | FStar_Syntax_Syntax.U_max us ->
          let uu____859 = FStar_List.map (subst_univ s) us in
          FStar_Syntax_Syntax.U_max uu____859
let tag_with_range :
  'Auu____868 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____868,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax=
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____901 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_bvar uu____901
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____903 = FStar_Syntax_Syntax.set_range_of_bv bv r1 in
                FStar_Syntax_Syntax.Tm_name uu____903
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv in
                let v1 =
                  let uu___110_909 = fv.FStar_Syntax_Syntax.fv_name in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___110_909.FStar_Syntax_Syntax.p)
                  } in
                let fv1 =
                  let uu___111_911 = fv in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___111_911.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___111_911.FStar_Syntax_Syntax.fv_qual)
                  } in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t' in
          let uu___112_913 = t in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___112_913.FStar_Syntax_Syntax.vars)
          }
let tag_lid_with_range :
  'Auu____922 .
    FStar_Ident.lident ->
      ('Auu____922,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident=
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____946 =
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r in
          FStar_Ident.set_lid_range l uu____946
let (mk_range
  :FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range)=
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' -> FStar_Range.set_use_range r r'
let rec (subst'
  :FStar_Syntax_Syntax.subst_ts ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s)) in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1064 ->
          let t0 = force_delayed_thunk t in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1074 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1079 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1084 -> tag_with_range t0 s
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
               let uu____1193 = mk_range t0.FStar_Syntax_Syntax.pos s in
               let uu____1194 =
                 let uu____1197 =
                   let uu____1198 =
                     subst_univ (FStar_Pervasives_Native.fst s) u in
                   FStar_Syntax_Syntax.Tm_type uu____1198 in
                 FStar_Syntax_Syntax.mk uu____1197 in
               uu____1194 FStar_Pervasives_Native.None uu____1193
           | uu____1208 ->
               let uu____1209 = mk_range t.FStar_Syntax_Syntax.pos s in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1209)
and (subst_flags'
  :FStar_Syntax_Syntax.subst_ts ->
     FStar_Syntax_Syntax.cflags Prims.list ->
       FStar_Syntax_Syntax.cflags Prims.list)=
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___108_1223  ->
              match uu___108_1223 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1227 = subst' s a in
                  FStar_Syntax_Syntax.DECREASES uu____1227
              | f -> f))
and (subst_comp_typ'
  :(FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                          FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 ->
     FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)=
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1261 ->
          let uu___113_1272 = t in
          let uu____1273 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs in
          let uu____1280 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s in
          let uu____1285 = subst' s t.FStar_Syntax_Syntax.result_typ in
          let uu____1288 =
            FStar_List.map
              (fun uu____1313  ->
                 match uu____1313 with
                 | (t1,imp) ->
                     let uu____1332 = subst' s t1 in (uu____1332, imp))
              t.FStar_Syntax_Syntax.effect_args in
          let uu____1337 = subst_flags' s t.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1273;
            FStar_Syntax_Syntax.effect_name = uu____1280;
            FStar_Syntax_Syntax.result_typ = uu____1285;
            FStar_Syntax_Syntax.effect_args = uu____1288;
            FStar_Syntax_Syntax.flags = uu____1337
          }
and (subst_comp'
  :(FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                          FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 ->
     FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)=
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1374 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1397 = subst' s t1 in
               let uu____1398 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_Total' uu____1397 uu____1398
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1417 = subst' s t1 in
               let uu____1418 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt in
               FStar_Syntax_Syntax.mk_GTotal' uu____1417 uu____1418
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1428 = subst_comp_typ' s ct in
               FStar_Syntax_Syntax.mk_Comp uu____1428)
let (shift
  :Prims.int ->
     FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)=
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1445 -> s
let (shift_subst
  :Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t)=
  fun n1  -> fun s  -> FStar_List.map (shift n1) s
let shift_subst' :
  'Auu____1466 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1466)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1466)
          FStar_Pervasives_Native.tuple2=
  fun n1  ->
    fun s  ->
      let uu____1493 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1)) in
      (uu____1493, (FStar_Pervasives_Native.snd s))
let subst_binder' :
  'Auu____1512 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1512) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1512) FStar_Pervasives_Native.tuple2=
  fun s  ->
    fun uu____1528  ->
      match uu____1528 with
      | (x,imp) ->
          let uu____1535 =
            let uu___114_1536 = x in
            let uu____1537 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___114_1536.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___114_1536.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1537
            } in
          (uu____1535, imp)
let subst_binders' :
  'Auu____1546 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1546) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1546) FStar_Pervasives_Native.tuple2
          Prims.list=
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1606 = shift_subst' i s in
                   subst_binder' uu____1606 b)))
let (subst_binders
  :FStar_Syntax_Syntax.subst_elt Prims.list ->
     FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)=
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs
let subst_arg' :
  'Auu____1637 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1637)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1637)
          FStar_Pervasives_Native.tuple2=
  fun s  ->
    fun uu____1657  ->
      match uu____1657 with
      | (t,imp) -> let uu____1670 = subst' s t in (uu____1670, imp)
let subst_args' :
  'Auu____1680 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1680)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1680)
          FStar_Pervasives_Native.tuple2 Prims.list=
  fun s  -> FStar_List.map (subst_arg' s)
let (subst_pat'
  :(FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                             FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 ->
     FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
       (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2)=
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1770 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1791 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1845  ->
                      fun uu____1846  ->
                        match (uu____1845, uu____1846) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1925 = aux n2 p2 in
                            (match uu____1925 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1)) in
            (match uu____1791 with
             | (pats1,n2) ->
                 ((let uu___115_1983 = p1 in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___115_1983.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___116_2009 = x in
              let uu____2010 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_2009.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_2009.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2010
              } in
            ((let uu___117_2016 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___117_2016.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___118_2032 = x in
              let uu____2033 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___118_2032.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___118_2032.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2033
              } in
            ((let uu___119_2039 = p1 in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___119_2039.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s in
            let x1 =
              let uu___120_2060 = x in
              let uu____2061 = subst' s1 x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_2060.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_2060.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2061
              } in
            let t01 = subst' s1 t0 in
            ((let uu___121_2070 = p1 in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___121_2070.FStar_Syntax_Syntax.p)
              }), n1) in
      aux (Prims.parse_int "0") p
let (push_subst_lcomp
  :FStar_Syntax_Syntax.subst_ts ->
     FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
       FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)=
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2092 =
            let uu___122_2093 = rc in
            let uu____2094 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___122_2093.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2094;
              FStar_Syntax_Syntax.residual_flags =
                (uu___122_2093.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____2092
let (push_subst
  :FStar_Syntax_Syntax.subst_ts ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2123 = mk_range t.FStar_Syntax_Syntax.pos s in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2123 in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2126 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2153 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2158 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2167 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2188 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2189 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2190 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us in
          let uu____2206 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1 in
          tag_with_range uu____2206 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2235 =
            let uu____2236 =
              let uu____2251 = subst' s t0 in
              let uu____2254 = subst_args' s args in (uu____2251, uu____2254) in
            FStar_Syntax_Syntax.Tm_app uu____2236 in
          mk1 uu____2235
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2349 = subst' s t1 in FStar_Util.Inl uu____2349
            | FStar_Util.Inr c ->
                let uu____2363 = subst_comp' s c in FStar_Util.Inr uu____2363 in
          let uu____2370 =
            let uu____2371 =
              let uu____2398 = subst' s t0 in
              let uu____2401 =
                let uu____2418 = FStar_Util.map_opt topt (subst' s) in
                (annot1, uu____2418) in
              (uu____2398, uu____2401, lopt) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2371 in
          mk1 uu____2370
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs in
          let s' = shift_subst' n1 s in
          let uu____2502 =
            let uu____2503 =
              let uu____2520 = subst_binders' s bs in
              let uu____2527 = subst' s' body in
              let uu____2530 = push_subst_lcomp s' lopt in
              (uu____2520, uu____2527, uu____2530) in
            FStar_Syntax_Syntax.Tm_abs uu____2503 in
          mk1 uu____2502
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs in
          let uu____2566 =
            let uu____2567 =
              let uu____2580 = subst_binders' s bs in
              let uu____2587 =
                let uu____2590 = shift_subst' n1 s in
                subst_comp' uu____2590 comp in
              (uu____2580, uu____2587) in
            FStar_Syntax_Syntax.Tm_arrow uu____2567 in
          mk1 uu____2566
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___123_2622 = x in
            let uu____2623 = subst' s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_2622.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_2622.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2623
            } in
          let phi1 =
            let uu____2629 = shift_subst' (Prims.parse_int "1") s in
            subst' uu____2629 phi in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0 in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2756  ->
                    match uu____2756 with
                    | (pat,wopt,branch) ->
                        let uu____2802 = subst_pat' s pat in
                        (match uu____2802 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2850 = subst' s1 w in
                                   FStar_Pervasives_Native.Some uu____2850 in
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
                      let uu____2935 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) in
                      if uu____2935
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___124_2950 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_2950.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_2950.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv in
                    let uu___125_2952 = lb in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_2952.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_2952.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    })) in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2979 =
            let uu____2980 =
              let uu____2987 = subst' s t0 in
              let uu____2990 =
                let uu____2991 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____2991 in
              (uu____2987, uu____2990) in
            FStar_Syntax_Syntax.Tm_meta uu____2980 in
          mk1 uu____2979
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3051 =
            let uu____3052 =
              let uu____3059 = subst' s t0 in
              let uu____3062 =
                let uu____3063 =
                  let uu____3070 = subst' s t1 in (m, uu____3070) in
                FStar_Syntax_Syntax.Meta_monadic uu____3063 in
              (uu____3059, uu____3062) in
            FStar_Syntax_Syntax.Tm_meta uu____3052 in
          mk1 uu____3051
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3089 =
            let uu____3090 =
              let uu____3097 = subst' s t0 in
              let uu____3100 =
                let uu____3101 =
                  let uu____3110 = subst' s t1 in (m1, m2, uu____3110) in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3101 in
              (uu____3097, uu____3100) in
            FStar_Syntax_Syntax.Tm_meta uu____3090 in
          mk1 uu____3089
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3123 =
            let uu____3124 = let uu____3131 = subst' s t1 in (uu____3131, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3124 in
          mk1 uu____3123
let rec (compress :FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun t  ->
    let t1 = force_delayed_thunk t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3195 = push_subst s t2 in compress uu____3195 in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3215 ->
        let t' = force_uvar t1 in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3219 -> compress t'
         | uu____3244 -> t')
let (subst
  :FStar_Syntax_Syntax.subst_elt Prims.list ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t
let (set_use_range
  :FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun r  ->
    fun t  ->
      subst'
        ([],
          (FStar_Pervasives_Native.Some
             (let uu___126_3284 = r in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___126_3284.FStar_Range.use_range)
              }))) t
let (subst_comp
  :FStar_Syntax_Syntax.subst_elt Prims.list ->
     FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
  fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t
let (closing_subst
  :FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list)=
  fun bs  ->
    let uu____3313 =
      FStar_List.fold_right
        (fun uu____3336  ->
           fun uu____3337  ->
             match (uu____3336, uu____3337) with
             | ((x,uu____3365),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0")) in
    FStar_All.pipe_right uu____3313 FStar_Pervasives_Native.fst
let open_binders' :
  'Auu____3400 .
    (FStar_Syntax_Syntax.bv,'Auu____3400) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3400) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2=
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___127_3506 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____3507 = subst o x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_3506.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_3506.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3507
            } in
          let o1 =
            let uu____3513 = shift_subst (Prims.parse_int "1") o in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3513 in
          let uu____3516 = aux bs' o1 in
          (match uu____3516 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2)) in
    aux bs []
let (open_binders
  :FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)=
  fun bs  ->
    let uu____3575 = open_binders' bs in
    FStar_Pervasives_Native.fst uu____3575
let (open_term'
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
         FStar_Pervasives_Native.tuple3)=
  fun bs  ->
    fun t  ->
      let uu____3610 = open_binders' bs in
      match uu____3610 with
      | (bs',opening) ->
          let uu____3647 = subst opening t in (bs', uu____3647, opening)
let (open_term
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2)=
  fun bs  ->
    fun t  ->
      let uu____3668 = open_term' bs t in
      match uu____3668 with | (b,t1,uu____3681) -> (b, t1)
let (open_comp
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.comp ->
       (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
         FStar_Pervasives_Native.tuple2)=
  fun bs  ->
    fun t  ->
      let uu____3694 = open_binders' bs in
      match uu____3694 with
      | (bs',opening) ->
          let uu____3729 = subst_comp opening t in (bs', uu____3729)
let (open_pat
  :FStar_Syntax_Syntax.pat ->
     (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
       FStar_Pervasives_Native.tuple2)=
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3810 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3839 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3931  ->
                    fun uu____3932  ->
                      match (uu____3931, uu____3932) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4080 = open_pat_aux sub2 renaming1 p2 in
                          (match uu____4080 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming)) in
          (match uu____3839 with
           | (pats1,sub2,renaming1) ->
               ((let uu___128_4250 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_4250.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___129_4269 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4270 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_4269.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_4269.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4270
            } in
          let sub2 =
            let uu____4276 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4276 in
          ((let uu___130_4290 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___130_4290.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___131_4299 = FStar_Syntax_Syntax.freshen_bv x in
            let uu____4300 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_4299.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_4299.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4300
            } in
          let sub2 =
            let uu____4306 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4306 in
          ((let uu___132_4320 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___132_4320.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_4334 = x in
            let uu____4335 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_4334.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_4334.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4335
            } in
          let t01 = subst sub1 t0 in
          ((let uu___134_4350 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_4350.FStar_Syntax_Syntax.p)
            }), sub1, renaming) in
    let uu____4353 = open_pat_aux [] [] p in
    match uu____4353 with | (p1,sub1,uu____4380) -> (p1, sub1)
let (open_branch :FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)=
  fun uu____4408  ->
    match uu____4408 with
    | (p,wopt,e) ->
        let uu____4428 = open_pat p in
        (match uu____4428 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4447 = subst opening w in
                   FStar_Pervasives_Native.Some uu____4447 in
             let e1 = subst opening e in (p1, wopt1, e1))
let (close
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun bs  ->
    fun t  -> let uu____4459 = closing_subst bs in subst uu____4459 t
let (close_comp
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
  fun bs  ->
    fun c  -> let uu____4470 = closing_subst bs in subst_comp uu____4470 c
let (close_binders
  :FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)=
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___135_4522 = x in
            let uu____4523 = subst s x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_4522.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_4522.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4523
            } in
          let s' =
            let uu____4529 = shift_subst (Prims.parse_int "1") s in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4529 in
          let uu____4532 = aux s' tl1 in (x1, imp) :: uu____4532 in
    aux [] bs
let (close_lcomp
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)=
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs in
      let uu___136_4554 = lc in
      let uu____4555 = subst s lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___136_4554.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4555;
        FStar_Syntax_Syntax.cflags =
          (uu___136_4554.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4560  ->
             let uu____4561 = lc.FStar_Syntax_Syntax.comp () in
             subst_comp s uu____4561)
      }
let (close_pat
  :FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
     (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                                Prims.list)
       FStar_Pervasives_Native.tuple2)=
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4609 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4632 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4698  ->
                    fun uu____4699  ->
                      match (uu____4698, uu____4699) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4802 = aux sub2 p2 in
                          (match uu____4802 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1)) in
          (match uu____4632 with
           | (pats1,sub2) ->
               ((let uu___137_4904 = p1 in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___137_4904.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___138_4923 = x in
            let uu____4924 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_4923.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_4923.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4924
            } in
          let sub2 =
            let uu____4930 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4930 in
          ((let uu___139_4938 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___139_4938.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___140_4943 = x in
            let uu____4944 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_4943.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_4943.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4944
            } in
          let sub2 =
            let uu____4950 = shift_subst (Prims.parse_int "1") sub1 in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4950 in
          ((let uu___141_4958 = p1 in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___141_4958.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_4968 = x in
            let uu____4969 = subst sub1 x.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_4968.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_4968.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4969
            } in
          let t01 = subst sub1 t0 in
          ((let uu___143_4978 = p1 in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___143_4978.FStar_Syntax_Syntax.p)
            }), sub1) in
    aux [] p
let (close_branch :FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)=
  fun uu____4984  ->
    match uu____4984 with
    | (p,wopt,e) ->
        let uu____5004 = close_pat p in
        (match uu____5004 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5035 = subst closing w in
                   FStar_Pervasives_Native.Some uu____5035 in
             let e1 = subst closing e in (p1, wopt1, e1))
let (univ_var_opening
  :FStar_Syntax_Syntax.univ_names ->
     (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                 Prims.list)
       FStar_Pervasives_Native.tuple2)=
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
let (univ_var_closing
  :FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)=
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
let (open_univ_vars
  :FStar_Syntax_Syntax.univ_names ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2)=
  fun us  ->
    fun t  ->
      let uu____5094 = univ_var_opening us in
      match uu____5094 with | (s,us') -> let t1 = subst s t in (us', t1)
let (open_univ_vars_comp
  :FStar_Syntax_Syntax.univ_names ->
     FStar_Syntax_Syntax.comp ->
       (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
         FStar_Pervasives_Native.tuple2)=
  fun us  ->
    fun c  ->
      let uu____5136 = univ_var_opening us in
      match uu____5136 with
      | (s,us') -> let uu____5159 = subst_comp s c in (us', uu____5159)
let (close_univ_vars
  :FStar_Syntax_Syntax.univ_names ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun us  -> fun t  -> let s = univ_var_closing us in subst s t
let (close_univ_vars_comp
  :FStar_Syntax_Syntax.univ_names ->
     FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)=
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i)))) in
      subst_comp s c
let (open_let_rec
  :FStar_Syntax_Syntax.letbinding Prims.list ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2)=
  fun lbs  ->
    fun t  ->
      let uu____5209 =
        let uu____5220 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5220
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5253  ->
                 match uu____5253 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5286 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       FStar_Syntax_Syntax.freshen_bv uu____5286 in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___144_5292 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___144_5292.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___144_5292.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___144_5292.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___144_5292.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], []) in
      match uu____5209 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5330 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5358  ->
                             match uu____5358 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening) in
                    match uu____5330 with
                    | (uu____5399,us,u_let_rec_opening) ->
                        let uu___145_5410 = lb in
                        let uu____5411 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5414 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___145_5410.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5411;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___145_5410.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5414
                        })) in
          let t1 = subst let_rec_opening t in (lbs2, t1)
let (close_let_rec
  :FStar_Syntax_Syntax.letbinding Prims.list ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2)=
  fun lbs  ->
    fun t  ->
      let uu____5438 =
        let uu____5445 = FStar_Syntax_Syntax.is_top_level lbs in
        if uu____5445
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5467  ->
                 match uu____5467 with
                 | (i,out) ->
                     let uu____5486 =
                       let uu____5489 =
                         let uu____5490 =
                           let uu____5495 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           (uu____5495, i) in
                         FStar_Syntax_Syntax.NM uu____5490 in
                       uu____5489 :: out in
                     ((i + (Prims.parse_int "1")), uu____5486)) lbs
            ((Prims.parse_int "0"), []) in
      match uu____5438 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5527 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5545  ->
                             match uu____5545 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing) in
                    match uu____5527 with
                    | (uu____5568,u_let_rec_closing) ->
                        let uu___146_5574 = lb in
                        let uu____5575 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____5578 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___146_5574.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___146_5574.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5575;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___146_5574.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5578
                        })) in
          let t1 = subst let_rec_closing t in (lbs1, t1)
let (close_tscheme
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)=
  fun binders  ->
    fun uu____5591  ->
      match uu____5591 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1") in
          let k = FStar_List.length us in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5616  ->
                   match uu____5616 with
                   | (x,uu____5622) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders in
          let t1 = subst s t in (us, t1)
let (close_univ_vars_tscheme
  :FStar_Syntax_Syntax.univ_names ->
     FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)=
  fun us  ->
    fun uu____5639  ->
      match uu____5639 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1") in
          let k = FStar_List.length us' in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us in
          let uu____5661 = subst s t in (us', uu____5661)
let (opening_of_binders
  :FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)=
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1") in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5684  ->
              match uu____5684 with
              | (x,uu____5690) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
let (closing_of_binders
  :FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)=
  fun bs  -> closing_subst bs