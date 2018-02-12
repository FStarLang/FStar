open Prims
let subst_to_string :
  'Auu____3 .
    (FStar_Syntax_Syntax.bv,'Auu____3) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____20 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____38  ->
              match uu____38 with
              | (b,uu____44) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____20 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____53 'Auu____54 .
    ('Auu____54 -> 'Auu____53 FStar_Pervasives_Native.option) ->
      'Auu____54 Prims.list ->
        ('Auu____54 Prims.list,'Auu____53) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____94 = f s0  in
          (match uu____94 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____120 'Auu____121 'Auu____122 .
    ('Auu____122 -> 'Auu____121 -> 'Auu____120) ->
      'Auu____120 ->
        ('Auu____122,'Auu____121) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____120
  =
  fun f  ->
    fun x  ->
      fun uu___34_146  ->
        match uu___34_146 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____174 'Auu____175 'Auu____176 .
    ('Auu____176 -> 'Auu____175 FStar_Pervasives_Native.option) ->
      'Auu____176 Prims.list ->
        ('Auu____176 Prims.list -> 'Auu____175 -> 'Auu____174) ->
          'Auu____174 -> 'Auu____174
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____220 = apply_until_some f s  in
          FStar_All.pipe_right uu____220 (map_some_curry g t)
  
let compose_subst :
  'Auu____243 'Auu____244 .
    ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____244 Prims.list,'Auu____243 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____313 ->
            FStar_Pervasives_Native.snd s2
        | uu____318 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____424 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____457) ->
        let uu____482 = FStar_Syntax_Unionfind.find uv  in
        (match uu____482 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____492 =
               let uu____495 = force_uvar' t'  in
               FStar_Pervasives_Native.fst uu____495  in
             (uu____492, true)
         | uu____506 -> (t, false))
    | uu____511 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____527 = force_uvar' t  in
    match uu____527 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____555 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____555, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____625 = FStar_ST.op_Bang m  in
        (match uu____625 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____746 = try_read_memo_aux t'  in
             (match uu____746 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____872 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____884 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____884
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____905 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____905 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____909 -> u)
    | uu____912 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___35_929  ->
           match uu___35_929 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____934 =
                 let uu____935 =
                   let uu____936 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____936  in
                 FStar_Syntax_Syntax.bv_to_name uu____935  in
               FStar_Pervasives_Native.Some uu____934
           | uu____937 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___36_954  ->
           match uu___36_954 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____959 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___40_962 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___40_962.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___40_962.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____959
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____971 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___37_987  ->
           match uu___37_987 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____992 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___38_1008  ->
           match uu___38_1008 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____1013 -> FStar_Pervasives_Native.None)
  
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u  in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____1035 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1045 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1045
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1049 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1049
  
let tag_with_range :
  'Auu____1055 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1055,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____1086 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1086
             in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____1089 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_bvar uu____1089
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____1091 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_name uu____1091
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___41_1097 = fv.FStar_Syntax_Syntax.fv_name  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___41_1097.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___42_1099 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___42_1099.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___42_1099.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___43_1101 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___43_1101.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____1107 .
    FStar_Ident.lident ->
      ('Auu____1107,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1131 =
            let uu____1132 = FStar_Range.use_range r  in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____1132
             in
          FStar_Ident.set_lid_range l uu____1131
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1146 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____1146
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1249 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1259 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1264 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1269 -> tag_with_range t0 s
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
               let uu____1378 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1379 =
                 let uu____1382 =
                   let uu____1383 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1383  in
                 FStar_Syntax_Syntax.mk uu____1382  in
               uu____1379 FStar_Pervasives_Native.None uu____1378
           | uu____1393 ->
               let uu____1394 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1394)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___39_1408  ->
              match uu___39_1408 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1412 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1412
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1446 ->
          let uu___44_1457 = t  in
          let uu____1458 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1465 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1470 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1473 =
            FStar_List.map
              (fun uu____1498  ->
                 match uu____1498 with
                 | (t1,imp) ->
                     let uu____1517 = subst' s t1  in (uu____1517, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1522 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1458;
            FStar_Syntax_Syntax.effect_name = uu____1465;
            FStar_Syntax_Syntax.result_typ = uu____1470;
            FStar_Syntax_Syntax.effect_args = uu____1473;
            FStar_Syntax_Syntax.flags = uu____1522
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1559 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1582 = subst' s t1  in
               let uu____1583 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1582 uu____1583
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1602 = subst' s t1  in
               let uu____1603 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1602 uu____1603
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1613 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1613)

let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1628 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1644 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1644)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1644)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1671 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1671, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1687 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1687) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1687) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1703  ->
      match uu____1703 with
      | (x,imp) ->
          let uu____1710 =
            let uu___45_1711 = x  in
            let uu____1712 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___45_1711.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___45_1711.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1712
            }  in
          (uu____1710, imp)
  
let subst_binders' :
  'Auu____1718 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1718) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1718) FStar_Pervasives_Native.tuple2
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
                  (let uu____1778 = shift_subst' i s  in
                   subst_binder' uu____1778 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1804 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1804)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1804)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1824  ->
      match uu____1824 with
      | (t,imp) -> let uu____1837 = subst' s t  in (uu____1837, imp)
  
let subst_args' :
  'Auu____1844 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1844)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1844)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1932 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1953 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2007  ->
                      fun uu____2008  ->
                        match (uu____2007, uu____2008) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2087 = aux n2 p2  in
                            (match uu____2087 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1953 with
             | (pats1,n2) ->
                 ((let uu___46_2145 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___46_2145.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___47_2171 = x  in
              let uu____2172 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___47_2171.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___47_2171.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2172
              }  in
            ((let uu___48_2178 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___48_2178.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___49_2194 = x  in
              let uu____2195 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___49_2194.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___49_2194.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2195
              }  in
            ((let uu___50_2201 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___50_2201.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___51_2222 = x  in
              let uu____2223 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___51_2222.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___51_2222.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2223
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___52_2232 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___52_2232.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2252 =
            let uu___53_2253 = rc  in
            let uu____2254 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___53_2253.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2254;
              FStar_Syntax_Syntax.residual_flags =
                (uu___53_2253.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2252
  
let (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2281 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2281  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2284 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2311 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2316 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2321 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2346 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2347 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2348 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2364 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2364 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2393 =
            let uu____2394 =
              let uu____2409 = subst' s t0  in
              let uu____2412 = subst_args' s args  in
              (uu____2409, uu____2412)  in
            FStar_Syntax_Syntax.Tm_app uu____2394  in
          mk1 uu____2393
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2507 = subst' s t1  in FStar_Util.Inl uu____2507
            | FStar_Util.Inr c ->
                let uu____2521 = subst_comp' s c  in
                FStar_Util.Inr uu____2521
             in
          let uu____2528 =
            let uu____2529 =
              let uu____2556 = subst' s t0  in
              let uu____2559 =
                let uu____2576 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2576)  in
              (uu____2556, uu____2559, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2529  in
          mk1 uu____2528
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2660 =
            let uu____2661 =
              let uu____2678 = subst_binders' s bs  in
              let uu____2685 = subst' s' body  in
              let uu____2688 = push_subst_lcomp s' lopt  in
              (uu____2678, uu____2685, uu____2688)  in
            FStar_Syntax_Syntax.Tm_abs uu____2661  in
          mk1 uu____2660
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2724 =
            let uu____2725 =
              let uu____2738 = subst_binders' s bs  in
              let uu____2745 =
                let uu____2748 = shift_subst' n1 s  in
                subst_comp' uu____2748 comp  in
              (uu____2738, uu____2745)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2725  in
          mk1 uu____2724
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___54_2780 = x  in
            let uu____2781 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___54_2780.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___54_2780.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2781
            }  in
          let phi1 =
            let uu____2787 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2787 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2914  ->
                    match uu____2914 with
                    | (pat,wopt,branch) ->
                        let uu____2960 = subst_pat' s pat  in
                        (match uu____2960 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3008 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3008
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs  in
          let sn = shift_subst' n1 s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3093 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3093
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___55_3108 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___55_3108.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___55_3108.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___56_3110 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___56_3110.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___56_3110.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3137 =
            let uu____3138 =
              let uu____3145 = subst' s t0  in
              let uu____3148 =
                let uu____3149 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3149  in
              (uu____3145, uu____3148)  in
            FStar_Syntax_Syntax.Tm_meta uu____3138  in
          mk1 uu____3137
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3209 =
            let uu____3210 =
              let uu____3217 = subst' s t0  in
              let uu____3220 =
                let uu____3221 =
                  let uu____3228 = subst' s t1  in (m, uu____3228)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3221  in
              (uu____3217, uu____3220)  in
            FStar_Syntax_Syntax.Tm_meta uu____3210  in
          mk1 uu____3209
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3247 =
            let uu____3248 =
              let uu____3255 = subst' s t0  in
              let uu____3258 =
                let uu____3259 =
                  let uu____3268 = subst' s t1  in (m1, m2, uu____3268)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3259  in
              (uu____3255, uu____3258)  in
            FStar_Syntax_Syntax.Tm_meta uu____3248  in
          mk1 uu____3247
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3281 =
            let uu____3282 = let uu____3289 = subst' s t1  in (uu____3289, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3282  in
          mk1 uu____3281
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
        ((let uu____3352 =
            let uu____3357 = push_subst s t'  in
            FStar_Pervasives_Native.Some uu____3357  in
          FStar_ST.op_Colon_Equals memo uu____3352);
         compress t1)
    | uu____3463 ->
        let uu____3464 = force_uvar t1  in
        (match uu____3464 with
         | (t',forced) ->
             (match t'.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3477 -> compress t'
              | uu____3502 -> t'))
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3529 =
        let uu____3530 =
          let uu____3533 =
            let uu____3534 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3534  in
          FStar_Pervasives_Native.Some uu____3533  in
        ([], uu____3530)  in
      subst' uu____3529 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3568 =
      FStar_List.fold_right
        (fun uu____3591  ->
           fun uu____3592  ->
             match (uu____3591, uu____3592) with
             | ((x,uu____3620),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3568 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3653 .
    (FStar_Syntax_Syntax.bv,'Auu____3653) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3653) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___57_3759 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3760 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___57_3759.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___57_3759.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3760
            }  in
          let o1 =
            let uu____3766 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3766
             in
          let uu____3769 = aux bs' o1  in
          (match uu____3769 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3827 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3827
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____3860 = open_binders' bs  in
      match uu____3860 with
      | (bs',opening) ->
          let uu____3897 = subst opening t  in (bs', uu____3897, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3916 = open_term' bs t  in
      match uu____3916 with | (b,t1,uu____3929) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3940 = open_binders' bs  in
      match uu____3940 with
      | (bs',opening) ->
          let uu____3975 = subst_comp opening t  in (bs', uu____3975)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4055 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4084 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4176  ->
                    fun uu____4177  ->
                      match (uu____4176, uu____4177) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4325 = open_pat_aux sub2 renaming1 p2  in
                          (match uu____4325 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming))
             in
          (match uu____4084 with
           | (pats1,sub2,renaming1) ->
               ((let uu___58_4495 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___58_4495.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___59_4514 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4515 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___59_4514.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___59_4514.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4515
            }  in
          let sub2 =
            let uu____4521 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4521
             in
          ((let uu___60_4535 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___60_4535.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___61_4544 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4545 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___61_4544.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___61_4544.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4545
            }  in
          let sub2 =
            let uu____4551 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4551
             in
          ((let uu___62_4565 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___62_4565.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___63_4579 = x  in
            let uu____4580 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___63_4579.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___63_4579.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4580
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___64_4595 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___64_4595.FStar_Syntax_Syntax.p)
            }), sub1, renaming)
       in
    let uu____4598 = open_pat_aux [] [] p  in
    match uu____4598 with | (p1,sub1,uu____4625) -> (p1, sub1)
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____4652  ->
    match uu____4652 with
    | (p,wopt,e) ->
        let uu____4672 = open_pat p  in
        (match uu____4672 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4691 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4691
                in
             let e1 = subst opening e  in (p1, wopt1, e1))
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4701 = closing_subst bs  in subst uu____4701 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4710 = closing_subst bs  in subst_comp uu____4710 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___65_4761 = x  in
            let uu____4762 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___65_4761.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___65_4761.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4762
            }  in
          let s' =
            let uu____4768 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4768
             in
          let uu____4771 = aux s' tl1  in (x1, imp) :: uu____4771
       in
    aux [] bs
  
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4793  ->
           let uu____4794 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4794)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4841 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4864 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4930  ->
                    fun uu____4931  ->
                      match (uu____4930, uu____4931) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5034 = aux sub2 p2  in
                          (match uu____5034 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4864 with
           | (pats1,sub2) ->
               ((let uu___66_5136 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___66_5136.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___67_5155 = x  in
            let uu____5156 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___67_5155.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___67_5155.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5156
            }  in
          let sub2 =
            let uu____5162 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5162
             in
          ((let uu___68_5170 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___68_5170.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___69_5175 = x  in
            let uu____5176 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___69_5175.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___69_5175.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5176
            }  in
          let sub2 =
            let uu____5182 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5182
             in
          ((let uu___70_5190 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___70_5190.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___71_5200 = x  in
            let uu____5201 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___71_5200.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___71_5200.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5201
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___72_5210 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___72_5210.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5215  ->
    match uu____5215 with
    | (p,wopt,e) ->
        let uu____5235 = close_pat p  in
        (match uu____5235 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5266 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5266
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun t  ->
      let uu____5321 = univ_var_opening us  in
      match uu____5321 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5361 = univ_var_opening us  in
      match uu____5361 with
      | (s,us') -> let uu____5384 = subst_comp s c  in (us', uu____5384)
  
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5428 =
        let uu____5439 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5439
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5472  ->
                 match uu____5472 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5505 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5505  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___73_5511 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___73_5511.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___73_5511.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___73_5511.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___73_5511.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5428 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5549 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5577  ->
                             match uu____5577 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5549 with
                    | (uu____5618,us,u_let_rec_opening) ->
                        let uu___74_5629 = lb  in
                        let uu____5630 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5633 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___74_5629.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5630;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___74_5629.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5633
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5655 =
        let uu____5662 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5662
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5684  ->
                 match uu____5684 with
                 | (i,out) ->
                     let uu____5703 =
                       let uu____5706 =
                         let uu____5707 =
                           let uu____5712 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5712, i)  in
                         FStar_Syntax_Syntax.NM uu____5707  in
                       uu____5706 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5703)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5655 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5744 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5762  ->
                             match uu____5762 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5744 with
                    | (uu____5785,u_let_rec_closing) ->
                        let uu___75_5791 = lb  in
                        let uu____5792 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5795 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___75_5791.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___75_5791.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5792;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___75_5791.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5795
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5806  ->
      match uu____5806 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5831  ->
                   match uu____5831 with
                   | (x,uu____5837) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5852  ->
      match uu____5852 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5874 = subst s t  in (us', uu____5874)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5884  ->
      match uu____5884 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5894 = subst s1 t  in (us, uu____5894)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5916  ->
              match uu____5916 with
              | (x,uu____5922) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 