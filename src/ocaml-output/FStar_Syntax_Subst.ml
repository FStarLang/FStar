open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____41  ->
              match uu____41 with
              | (b,uu____47) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____60 'Auu____61 .
    ('Auu____60 -> 'Auu____61 FStar_Pervasives_Native.option) ->
      'Auu____60 Prims.list ->
        ('Auu____60 Prims.list,'Auu____61) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____103 = f s0  in
          (match uu____103 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____135 'Auu____136 'Auu____137 .
    ('Auu____135 -> 'Auu____136 -> 'Auu____137) ->
      'Auu____137 ->
        ('Auu____135,'Auu____136) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____137
  =
  fun f  ->
    fun x  ->
      fun uu___36_164  ->
        match uu___36_164 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____199 'Auu____200 'Auu____201 .
    ('Auu____199 -> 'Auu____200 FStar_Pervasives_Native.option) ->
      'Auu____199 Prims.list ->
        ('Auu____199 Prims.list -> 'Auu____200 -> 'Auu____201) ->
          'Auu____201 -> 'Auu____201
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____249 = apply_until_some f s  in
          FStar_All.pipe_right uu____249 (map_some_curry g t)
  
let compose_subst :
  'Auu____276 'Auu____277 .
    ('Auu____276 Prims.list,'Auu____277 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____276 Prims.list,'Auu____277 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____276 Prims.list,'Auu____277 FStar_Pervasives_Native.option)
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
        | FStar_Pervasives_Native.Some uu____348 ->
            FStar_Pervasives_Native.snd s2
        | uu____353 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let delay :
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
      | uu____463 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____498) ->
        let uu____523 = FStar_Syntax_Unionfind.find uv  in
        (match uu____523 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____533 =
               let uu____536 = force_uvar' t'  in
               FStar_Pervasives_Native.fst uu____536  in
             (uu____533, true)
         | uu____547 -> (t, false))
    | uu____552 -> (t, false)
  
let force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____570 = force_uvar' t  in
    match uu____570 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____598 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____598, forced))
  
let rec try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____670 = FStar_ST.op_Bang m  in
        (match uu____670 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____743 = try_read_memo_aux t'  in
             (match uu____743 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____821 -> (t, false)
  
let try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let uu____835 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____835
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____858 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____858 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____862 -> u)
    | uu____865 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___37_886  ->
           match uu___37_886 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____891 =
                 let uu____892 =
                   let uu____893 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____893  in
                 FStar_Syntax_Syntax.bv_to_name uu____892  in
               FStar_Pervasives_Native.Some uu____891
           | uu____894 -> FStar_Pervasives_Native.None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___38_915  ->
           match uu___38_915 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____920 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___42_923 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___42_923.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___42_923.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____920
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____932 -> FStar_Pervasives_Native.None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___39_952  ->
           match uu___39_952 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____957 -> FStar_Pervasives_Native.None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___40_977  ->
           match uu___40_977 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____982 -> FStar_Pervasives_Native.None)
  
let rec subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
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
      | FStar_Syntax_Syntax.U_unif uu____1008 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1018 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1018
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1022 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1022
  
let tag_with_range :
  'Auu____1031 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1031,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____1064 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1064
             in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____1067 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_bvar uu____1067
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____1069 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_name uu____1069
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___43_1075 = fv.FStar_Syntax_Syntax.fv_name  in
                  let uu____1076 = FStar_Ident.set_lid_range l r1  in
                  {
                    FStar_Syntax_Syntax.v = uu____1076;
                    FStar_Syntax_Syntax.p =
                      (uu___43_1075.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___44_1078 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___44_1078.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___44_1078.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___45_1080 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___45_1080.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____1089 .
    FStar_Ident.lident ->
      ('Auu____1089,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1115 =
            let uu____1116 = FStar_Ident.range_of_lid l  in
            let uu____1117 = FStar_Range.use_range r  in
            FStar_Range.set_use_range uu____1116 uu____1117  in
          FStar_Ident.set_lid_range l uu____1115
  
let mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1135 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____1135
  
let rec subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1259 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1269 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1274 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1279 -> tag_with_range t0 s
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
               let uu____1388 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1389 =
                 let uu____1396 =
                   let uu____1397 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1397  in
                 FStar_Syntax_Syntax.mk uu____1396  in
               uu____1389 FStar_Pervasives_Native.None uu____1388
           | uu____1407 ->
               let uu____1408 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1408)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___41_1422  ->
              match uu___41_1422 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1426 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1426
              | f -> f))

and subst_comp_typ' :
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
      | uu____1460 ->
          let uu___46_1471 = t  in
          let uu____1472 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1479 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1484 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1487 =
            FStar_List.map
              (fun uu____1512  ->
                 match uu____1512 with
                 | (t1,imp) ->
                     let uu____1531 = subst' s t1  in (uu____1531, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1536 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1472;
            FStar_Syntax_Syntax.effect_name = uu____1479;
            FStar_Syntax_Syntax.result_typ = uu____1484;
            FStar_Syntax_Syntax.effect_args = uu____1487;
            FStar_Syntax_Syntax.flags = uu____1536
          }

and subst_comp' :
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
      | uu____1573 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1596 = subst' s t1  in
               let uu____1597 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1596 uu____1597
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1616 = subst' s t1  in
               let uu____1617 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1616 uu____1617
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1627 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1627)

let shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1646 -> s
  
let shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1669 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1669)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1669)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1698 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1698, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1717 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1717) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1717) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1735  ->
      match uu____1735 with
      | (x,imp) ->
          let uu____1742 =
            let uu___47_1743 = x  in
            let uu____1744 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___47_1743.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___47_1743.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1744
            }  in
          (uu____1742, imp)
  
let subst_binders' :
  'Auu____1753 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1753) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1753) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.lift_native_int (0))
                then subst_binder' s b
                else
                  (let uu____1815 = shift_subst' i s  in
                   subst_binder' uu____1815 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1848 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1848)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1848)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1870  ->
      match uu____1870 with
      | (t,imp) -> let uu____1883 = subst' s t  in (uu____1883, imp)
  
let subst_args' :
  'Auu____1893 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1893)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1893)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let subst_pat' :
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
        | FStar_Syntax_Syntax.Pat_constant uu____1992 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____2013 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2067  ->
                      fun uu____2068  ->
                        match (uu____2067, uu____2068) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2147 = aux n2 p2  in
                            (match uu____2147 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____2013 with
             | (pats1,n2) ->
                 ((let uu___48_2205 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___48_2205.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___49_2231 = x  in
              let uu____2232 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___49_2231.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___49_2231.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2232
              }  in
            ((let uu___50_2238 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___50_2238.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.lift_native_int (1))))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___51_2254 = x  in
              let uu____2255 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___51_2254.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___51_2254.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2255
              }  in
            ((let uu___52_2261 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___52_2261.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.lift_native_int (1))))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___53_2282 = x  in
              let uu____2283 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___53_2282.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___53_2282.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2283
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___54_2292 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___54_2292.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.lift_native_int (0)) p
  
let push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2316 =
            let uu___55_2317 = rc  in
            let uu____2318 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___55_2317.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2318;
              FStar_Syntax_Syntax.residual_flags =
                (uu___55_2317.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2316
  
let push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2351 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2351  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2354 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2382 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2387 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2392 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2417 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2418 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2419 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2435 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2435 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2464 =
            let uu____2465 =
              let uu____2480 = subst' s t0  in
              let uu____2483 = subst_args' s args  in
              (uu____2480, uu____2483)  in
            FStar_Syntax_Syntax.Tm_app uu____2465  in
          mk1 uu____2464
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2578 = subst' s t1  in FStar_Util.Inl uu____2578
            | FStar_Util.Inr c ->
                let uu____2592 = subst_comp' s c  in
                FStar_Util.Inr uu____2592
             in
          let uu____2599 =
            let uu____2600 =
              let uu____2627 = subst' s t0  in
              let uu____2630 =
                let uu____2647 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2647)  in
              (uu____2627, uu____2630, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2600  in
          mk1 uu____2599
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2731 =
            let uu____2732 =
              let uu____2749 = subst_binders' s bs  in
              let uu____2756 = subst' s' body  in
              let uu____2759 = push_subst_lcomp s' lopt  in
              (uu____2749, uu____2756, uu____2759)  in
            FStar_Syntax_Syntax.Tm_abs uu____2732  in
          mk1 uu____2731
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2795 =
            let uu____2796 =
              let uu____2809 = subst_binders' s bs  in
              let uu____2816 =
                let uu____2819 = shift_subst' n1 s  in
                subst_comp' uu____2819 comp  in
              (uu____2809, uu____2816)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2796  in
          mk1 uu____2795
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___56_2851 = x  in
            let uu____2852 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___56_2851.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___56_2851.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2852
            }  in
          let phi1 =
            let uu____2858 = shift_subst' (Prims.lift_native_int (1)) s  in
            subst' uu____2858 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2985  ->
                    match uu____2985 with
                    | (pat,wopt,branch) ->
                        let uu____3031 = subst_pat' s pat  in
                        (match uu____3031 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3079 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3079
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
                      let uu____3164 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3164
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___57_3179 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___57_3179.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___57_3179.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___58_3181 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___58_3181.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___58_3181.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___58_3181.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___58_3181.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3208 =
            let uu____3209 =
              let uu____3216 = subst' s t0  in
              let uu____3219 =
                let uu____3220 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3220  in
              (uu____3216, uu____3219)  in
            FStar_Syntax_Syntax.Tm_meta uu____3209  in
          mk1 uu____3208
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3280 =
            let uu____3281 =
              let uu____3288 = subst' s t0  in
              let uu____3291 =
                let uu____3292 =
                  let uu____3299 = subst' s t1  in (m, uu____3299)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3292  in
              (uu____3288, uu____3291)  in
            FStar_Syntax_Syntax.Tm_meta uu____3281  in
          mk1 uu____3280
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3318 =
            let uu____3319 =
              let uu____3326 = subst' s t0  in
              let uu____3329 =
                let uu____3330 =
                  let uu____3339 = subst' s t1  in (m1, m2, uu____3339)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3330  in
              (uu____3326, uu____3329)  in
            FStar_Syntax_Syntax.Tm_meta uu____3319  in
          mk1 uu____3318
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3354 =
                 let uu____3355 =
                   let uu____3362 = subst' s tm  in (uu____3362, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3355  in
               mk1 uu____3354
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3376 =
            let uu____3377 = let uu____3384 = subst' s t1  in (uu____3384, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3377  in
          mk1 uu____3376
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = try_read_memo t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
        ((let uu____3449 =
            let uu____3454 = push_subst s t'  in
            FStar_Pervasives_Native.Some uu____3454  in
          FStar_ST.op_Colon_Equals memo uu____3449);
         compress t1)
    | uu____3512 ->
        let uu____3513 = force_uvar t1  in
        (match uu____3513 with
         | (t',forced) ->
             (match t'.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3526 -> compress t'
              | uu____3551 -> t'))
  
let subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      let uu____3586 =
        let uu____3587 =
          let uu____3590 =
            let uu____3591 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3591  in
          FStar_Pervasives_Native.Some uu____3590  in
        ([], uu____3587)  in
      subst' uu____3586 t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3631 =
      FStar_List.fold_right
        (fun uu____3654  ->
           fun uu____3655  ->
             match (uu____3654, uu____3655) with
             | ((x,uu____3683),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.lift_native_int (1))))) bs
        ([], (Prims.lift_native_int (0)))
       in
    FStar_All.pipe_right uu____3631 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3718 .
    (FStar_Syntax_Syntax.bv,'Auu____3718) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3718) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___59_3829 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3830 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___59_3829.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___59_3829.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3830
            }  in
          let o1 =
            let uu____3836 = shift_subst (Prims.lift_native_int (1)) o  in
            (FStar_Syntax_Syntax.DB ((Prims.lift_native_int (0)), x')) ::
              uu____3836
             in
          let uu____3839 = aux bs' o1  in
          (match uu____3839 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let open_binders : FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3899 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3899
  
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3936 = open_binders' bs  in
      match uu____3936 with
      | (bs',opening) ->
          let uu____3973 = subst opening t  in (bs', uu____3973, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3996 = open_term' bs t  in
      match uu____3996 with | (b,t1,uu____4009) -> (b, t1)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____4024 = open_binders' bs  in
      match uu____4024 with
      | (bs',opening) ->
          let uu____4059 = subst_comp opening t  in (bs', uu____4059)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4114 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4137 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4203  ->
                    fun uu____4204  ->
                      match (uu____4203, uu____4204) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4307 = open_pat_aux sub2 p2  in
                          (match uu____4307 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4137 with
           | (pats1,sub2) ->
               ((let uu___60_4409 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___60_4409.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___61_4428 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4429 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___61_4428.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___61_4428.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4429
            }  in
          let sub2 =
            let uu____4435 = shift_subst (Prims.lift_native_int (1)) sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.lift_native_int (0)), x')) ::
              uu____4435
             in
          ((let uu___62_4443 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___62_4443.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___63_4448 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4449 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___63_4448.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___63_4448.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4449
            }  in
          let sub2 =
            let uu____4455 = shift_subst (Prims.lift_native_int (1)) sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.lift_native_int (0)), x')) ::
              uu____4455
             in
          ((let uu___64_4463 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___64_4463.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___65_4473 = x  in
            let uu____4474 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___65_4473.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___65_4473.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4474
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___66_4483 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___66_4483.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4494  ->
    match uu____4494 with
    | (p,wopt,e) ->
        let uu____4518 = open_pat p  in
        (match uu____4518 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4541 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4541
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun br  ->
    let uu____4558 = open_branch' br  in
    match uu____4558 with | (br1,uu____4564) -> br1
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4575 = closing_subst bs  in subst uu____4575 t
  
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4588 = closing_subst bs  in subst_comp uu____4588 c
  
let close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___67_4645 = x  in
            let uu____4646 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___67_4645.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___67_4645.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4646
            }  in
          let s' =
            let uu____4652 = shift_subst (Prims.lift_native_int (1)) s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.lift_native_int (0)))) ::
              uu____4652
             in
          let uu____4655 = aux s' tl1  in (x1, imp) :: uu____4655
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4681  ->
           let uu____4682 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4682)
  
let close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4735 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4758 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4824  ->
                    fun uu____4825  ->
                      match (uu____4824, uu____4825) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4928 = aux sub2 p2  in
                          (match uu____4928 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4758 with
           | (pats1,sub2) ->
               ((let uu___68_5030 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___68_5030.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___69_5049 = x  in
            let uu____5050 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___69_5049.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___69_5049.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5050
            }  in
          let sub2 =
            let uu____5056 = shift_subst (Prims.lift_native_int (1)) sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.lift_native_int (0)))) ::
              uu____5056
             in
          ((let uu___70_5064 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___70_5064.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___71_5069 = x  in
            let uu____5070 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___71_5069.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___71_5069.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5070
            }  in
          let sub2 =
            let uu____5076 = shift_subst (Prims.lift_native_int (1)) sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.lift_native_int (0)))) ::
              uu____5076
             in
          ((let uu___72_5084 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___72_5084.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___73_5094 = x  in
            let uu____5095 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___73_5094.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___73_5094.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5095
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___74_5104 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___74_5104.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____5111  ->
    match uu____5111 with
    | (p,wopt,e) ->
        let uu____5131 = close_pat p  in
        (match uu____5131 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5162 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5162
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.lift_native_int (1))  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.lift_native_int (1))  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun t  ->
      let uu____5225 = univ_var_opening us  in
      match uu____5225 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5269 = univ_var_opening us  in
      match uu____5269 with
      | (s,us') -> let uu____5292 = subst_comp s c  in (us', uu____5292)
  
let close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.lift_native_int (1))  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5348 =
        let uu____5359 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5359
        then ((Prims.lift_native_int (0)), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5392  ->
                 match uu____5392 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5425 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5425  in
                     ((i + (Prims.lift_native_int (1))),
                       ((let uu___75_5431 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___75_5431.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___75_5431.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___75_5431.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___75_5431.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___75_5431.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___75_5431.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.lift_native_int (0)), [], [])
         in
      match uu____5348 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5469 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5497  ->
                             match uu____5497 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.lift_native_int (1))), (u1 ::
                                   us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5469 with
                    | (uu____5538,us,u_let_rec_opening) ->
                        let uu___76_5549 = lb  in
                        let uu____5550 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5553 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___76_5549.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5550;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___76_5549.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5553;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___76_5549.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___76_5549.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5579 =
        let uu____5586 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5586
        then ((Prims.lift_native_int (0)), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5608  ->
                 match uu____5608 with
                 | (i,out) ->
                     let uu____5627 =
                       let uu____5630 =
                         let uu____5631 =
                           let uu____5636 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5636, i)  in
                         FStar_Syntax_Syntax.NM uu____5631  in
                       uu____5630 :: out  in
                     ((i + (Prims.lift_native_int (1))), uu____5627)) lbs
            ((Prims.lift_native_int (0)), [])
         in
      match uu____5579 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5668 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5686  ->
                             match uu____5686 with
                             | (i,out) ->
                                 ((i + (Prims.lift_native_int (1))),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5668 with
                    | (uu____5709,u_let_rec_closing) ->
                        let uu___77_5715 = lb  in
                        let uu____5716 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5719 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___77_5715.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___77_5715.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5716;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___77_5715.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5719;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___77_5715.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___77_5715.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5734  ->
      match uu____5734 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.lift_native_int (1))
             in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5759  ->
                   match uu____5759 with
                   | (x,uu____5765) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5784  ->
      match uu____5784 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.lift_native_int (1))  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5806 = subst s t  in (us', uu____5806)
  
let subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun s  ->
    fun uu____5820  ->
      match uu____5820 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5830 = subst s1 t  in (us, uu____5830)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.lift_native_int (1))  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5854  ->
              match uu____5854 with
              | (x,uu____5860) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs 
let open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun b  ->
    fun t  ->
      let uu____5880 = open_term [b] t  in
      match uu____5880 with
      | (b1::[],t1) -> (b1, t1)
      | uu____5913 -> failwith "impossible: open_term_1"
  
let open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bvs  ->
    fun t  ->
      let uu____5942 =
        let uu____5947 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____5947 t  in
      match uu____5942 with
      | (bs,t1) ->
          let uu____5956 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____5956, t1)
  
let open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bv  ->
    fun t  ->
      let uu____5979 = open_term_bvs [bv] t  in
      match uu____5979 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____5994 -> failwith "impossible: open_term_bv"
  