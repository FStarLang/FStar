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
      fun uu___64_164  ->
        match uu___64_164 with
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
      | uu____451 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____474;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____475;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____476;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____477;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____478;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____479;_},s)
        ->
        let uu____505 = FStar_Syntax_Unionfind.find uv  in
        (match uu____505 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____515 =
               let uu____518 =
                 let uu____525 = delay t' ([s], FStar_Pervasives_Native.None)
                    in
                 force_uvar' uu____525  in
               FStar_Pervasives_Native.fst uu____518  in
             (uu____515, true)
         | uu____542 -> (t, false))
    | uu____547 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____563 = force_uvar' t  in
    match uu____563 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____585 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____585, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____657 = FStar_ST.op_Bang m  in
        (match uu____657 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____730 = try_read_memo_aux t'  in
             (match uu____730 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____808 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____822 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____822
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____845 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____845 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____849 -> u)
    | uu____852 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___65_873  ->
           match uu___65_873 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____878 =
                 let uu____879 =
                   let uu____880 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____880  in
                 FStar_Syntax_Syntax.bv_to_name uu____879  in
               FStar_Pervasives_Native.Some uu____878
           | uu____881 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___66_906  ->
           match uu___66_906 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____913 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___72_918 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___72_918.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___72_918.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____913
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____929 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___67_951  ->
           match uu___67_951 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____956 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___68_976  ->
           match uu___68_976 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____981 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1007 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1017 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1017
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1021 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1021
  
let tag_with_range :
  'Auu____1030 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1030,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____1063 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1063
             in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____1066 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_bvar uu____1066
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____1068 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_name uu____1068
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___73_1074 = fv.FStar_Syntax_Syntax.fv_name  in
                  let uu____1075 = FStar_Ident.set_lid_range l r1  in
                  {
                    FStar_Syntax_Syntax.v = uu____1075;
                    FStar_Syntax_Syntax.p =
                      (uu___73_1074.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___74_1077 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___74_1077.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___74_1077.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___75_1079 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___75_1079.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____1088 .
    FStar_Ident.lident ->
      ('Auu____1088,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1114 =
            let uu____1115 = FStar_Ident.range_of_lid l  in
            let uu____1116 = FStar_Range.use_range r  in
            FStar_Range.set_use_range uu____1115 uu____1116  in
          FStar_Ident.set_lid_range l uu____1114
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1134 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____1134
  
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
      | uu____1258 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1268 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1273 -> tag_with_range t0 s
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
               let uu____1356 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1357 =
                 let uu____1364 =
                   let uu____1365 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1365  in
                 FStar_Syntax_Syntax.mk uu____1364  in
               uu____1357 FStar_Pervasives_Native.None uu____1356
           | uu____1375 ->
               let uu____1376 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1376)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___69_1388  ->
              match uu___69_1388 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1392 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1392
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
      | uu____1426 ->
          let uu___76_1437 = t  in
          let uu____1438 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1445 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1450 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1453 =
            FStar_List.map
              (fun uu____1478  ->
                 match uu____1478 with
                 | (t1,imp) ->
                     let uu____1497 = subst' s t1  in (uu____1497, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1502 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1438;
            FStar_Syntax_Syntax.effect_name = uu____1445;
            FStar_Syntax_Syntax.result_typ = uu____1450;
            FStar_Syntax_Syntax.effect_args = uu____1453;
            FStar_Syntax_Syntax.flags = uu____1502
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
      | uu____1539 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1562 = subst' s t1  in
               let uu____1563 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1562 uu____1563
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1582 = subst' s t1  in
               let uu____1583 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1582 uu____1583
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1593 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1593)

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
      | FStar_Syntax_Syntax.NT uu____1612 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1635 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1635)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1635)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1664 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1664, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1683 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1683) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1683) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1701  ->
      match uu____1701 with
      | (x,imp) ->
          let uu____1708 =
            let uu___77_1709 = x  in
            let uu____1710 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___77_1709.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___77_1709.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1710
            }  in
          (uu____1708, imp)
  
let subst_binders' :
  'Auu____1719 .
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____1719) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1719) FStar_Pervasives_Native.tuple2
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
                  (let uu____1801 = shift_subst' i s  in
                   subst_binder' uu____1801 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1834 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1834)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1834)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1856  ->
      match uu____1856 with
      | (t,imp) -> let uu____1869 = subst' s t  in (uu____1869, imp)
  
let subst_args' :
  'Auu____1879 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1879)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1879)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1978 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1997 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2051  ->
                      fun uu____2052  ->
                        match (uu____2051, uu____2052) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2131 = aux n2 p2  in
                            (match uu____2131 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1997 with
             | (pats1,n2) ->
                 ((let uu___78_2187 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___78_2187.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___79_2217 = x  in
              let uu____2218 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___79_2217.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___79_2217.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2218
              }  in
            ((let uu___80_2222 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___80_2222.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___81_2238 = x  in
              let uu____2239 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___81_2238.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___81_2238.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2239
              }  in
            ((let uu___82_2243 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___82_2243.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___83_2264 = x  in
              let uu____2265 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___83_2264.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___83_2264.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2265
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___84_2272 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___84_2272.FStar_Syntax_Syntax.p)
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
          let uu____2296 =
            let uu___85_2297 = rc  in
            let uu____2298 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___85_2297.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2298;
              FStar_Syntax_Syntax.residual_flags =
                (uu___85_2297.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2296
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.subst_ts ->
        FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____2349  ->
                  match uu____2349 with
                  | (x',uu____2355) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___71_2367 =
          match uu___71_2367 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___70_2398  ->
                        match uu___70_2398 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2407 = should_retain x  in
                            if uu____2407
                            then
                              let uu____2410 =
                                let uu____2411 =
                                  let uu____2418 =
                                    delay t
                                      (rest, FStar_Pervasives_Native.None)
                                     in
                                  (x, uu____2418)  in
                                FStar_Syntax_Syntax.NT uu____2411  in
                              [uu____2410]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2432 = should_retain x  in
                            if uu____2432
                            then
                              let uu____2435 =
                                let uu____2436 =
                                  let uu____2443 =
                                    let uu____2446 =
                                      FStar_Syntax_Syntax.bv_to_tm
                                        (let uu___86_2451 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___86_2451.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index = i;
                                           FStar_Syntax_Syntax.sort =
                                             (uu___86_2451.FStar_Syntax_Syntax.sort)
                                         })
                                       in
                                    delay uu____2446
                                      (rest, FStar_Pervasives_Native.None)
                                     in
                                  (x, uu____2443)  in
                                FStar_Syntax_Syntax.NT uu____2436  in
                              [uu____2435]
                            else []
                        | uu____2461 -> []))
                 in
              let uu____2462 = aux rest  in FStar_List.append hd1 uu____2462
           in
        aux (s0 :: (FStar_Pervasives_Native.fst s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2497 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2497  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2500 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2528 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2533 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2548 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2548 with
           | FStar_Pervasives_Native.None  ->
               let uu____2553 =
                 let uu___87_2556 = t  in
                 let uu____2559 =
                   let uu____2560 =
                     let uu____2567 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2567)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2560  in
                 {
                   FStar_Syntax_Syntax.n = uu____2559;
                   FStar_Syntax_Syntax.pos =
                     (uu___87_2556.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___87_2556.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2553 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst
                 (compose_subst ([s0], FStar_Pervasives_Native.None) s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2589 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2590 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2591 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2607 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2607 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2636 =
            let uu____2637 =
              let uu____2652 = subst' s t0  in
              let uu____2655 = subst_args' s args  in
              (uu____2652, uu____2655)  in
            FStar_Syntax_Syntax.Tm_app uu____2637  in
          mk1 uu____2636
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2750 = subst' s t1  in FStar_Util.Inl uu____2750
            | FStar_Util.Inr c ->
                let uu____2764 = subst_comp' s c  in
                FStar_Util.Inr uu____2764
             in
          let uu____2771 =
            let uu____2772 =
              let uu____2799 = subst' s t0  in
              let uu____2802 =
                let uu____2819 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2819)  in
              (uu____2799, uu____2802, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2772  in
          mk1 uu____2771
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2903 =
            let uu____2904 =
              let uu____2921 = subst_binders' s bs  in
              let uu____2928 = subst' s' body  in
              let uu____2931 = push_subst_lcomp s' lopt  in
              (uu____2921, uu____2928, uu____2931)  in
            FStar_Syntax_Syntax.Tm_abs uu____2904  in
          mk1 uu____2903
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2967 =
            let uu____2968 =
              let uu____2981 = subst_binders' s bs  in
              let uu____2988 =
                let uu____2991 = shift_subst' n1 s  in
                subst_comp' uu____2991 comp  in
              (uu____2981, uu____2988)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2968  in
          mk1 uu____2967
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___88_3023 = x  in
            let uu____3024 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___88_3023.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___88_3023.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3024
            }  in
          let phi1 =
            let uu____3030 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3030 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3161  ->
                    match uu____3161 with
                    | (pat,wopt,branch) ->
                        let uu____3207 = subst_pat' s pat  in
                        (match uu____3207 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3255 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3255
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
                      let uu____3342 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3342
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___89_3357 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___89_3357.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___89_3357.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___90_3359 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___90_3359.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___90_3359.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___90_3359.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___90_3359.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3386 =
            let uu____3387 =
              let uu____3394 = subst' s t0  in
              let uu____3397 =
                let uu____3398 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3398  in
              (uu____3394, uu____3397)  in
            FStar_Syntax_Syntax.Tm_meta uu____3387  in
          mk1 uu____3386
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3458 =
            let uu____3459 =
              let uu____3466 = subst' s t0  in
              let uu____3469 =
                let uu____3470 =
                  let uu____3477 = subst' s t1  in (m, uu____3477)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3470  in
              (uu____3466, uu____3469)  in
            FStar_Syntax_Syntax.Tm_meta uu____3459  in
          mk1 uu____3458
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3496 =
            let uu____3497 =
              let uu____3504 = subst' s t0  in
              let uu____3507 =
                let uu____3508 =
                  let uu____3517 = subst' s t1  in (m1, m2, uu____3517)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3508  in
              (uu____3504, uu____3507)  in
            FStar_Syntax_Syntax.Tm_meta uu____3497  in
          mk1 uu____3496
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3532 =
                 let uu____3533 =
                   let uu____3540 = subst' s tm  in (uu____3540, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3533  in
               mk1 uu____3532
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3554 =
            let uu____3555 = let uu____3562 = subst' s t1  in (uu____3562, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3555  in
          mk1 uu____3554
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3575 = force_uvar t1  in
    match uu____3575 with
    | (t2,uu____3581) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3634 =
                 let uu____3639 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3639  in
               FStar_ST.op_Colon_Equals memo uu____3634);
              compress t2)
         | uu____3697 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3732 =
        let uu____3733 =
          let uu____3736 =
            let uu____3737 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3737  in
          FStar_Pervasives_Native.Some uu____3736  in
        ([], uu____3733)  in
      subst' uu____3732 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3777 =
      FStar_List.fold_right
        (fun uu____3800  ->
           fun uu____3801  ->
             match (uu____3800, uu____3801) with
             | ((x,uu____3829),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3777 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3864 .
    (FStar_Syntax_Syntax.bv,'Auu____3864) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3864) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___91_3975 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3976 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___91_3975.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___91_3975.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3976
            }  in
          let o1 =
            let uu____3982 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3982
             in
          let uu____3985 = aux bs' o1  in
          (match uu____3985 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4045 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4045
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4082 = open_binders' bs  in
      match uu____4082 with
      | (bs',opening) ->
          let uu____4119 = subst opening t  in (bs', uu____4119, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4134 = open_term' bs t  in
      match uu____4134 with | (b,t1,uu____4147) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4162 = open_binders' bs  in
      match uu____4162 with
      | (bs',opening) ->
          let uu____4197 = subst_comp opening t  in (bs', uu____4197)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4246 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4269 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4335  ->
                    fun uu____4336  ->
                      match (uu____4335, uu____4336) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4439 = open_pat_aux sub2 p2  in
                          (match uu____4439 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4269 with
           | (pats1,sub2) ->
               ((let uu___92_4541 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___92_4541.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___93_4560 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4561 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___93_4560.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___93_4560.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4561
            }  in
          let sub2 =
            let uu____4567 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4567
             in
          ((let uu___94_4575 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___94_4575.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___95_4580 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4581 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___95_4580.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___95_4580.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4581
            }  in
          let sub2 =
            let uu____4587 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4587
             in
          ((let uu___96_4595 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___96_4595.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___97_4605 = x  in
            let uu____4606 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___97_4605.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___97_4605.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4606
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___98_4615 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___98_4615.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4628  ->
    match uu____4628 with
    | (p,wopt,e) ->
        let uu____4652 = open_pat p  in
        (match uu____4652 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4681 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4681
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4696 = open_branch' br  in
    match uu____4696 with | (br1,uu____4702) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4713 = closing_subst bs  in subst uu____4713 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4726 = closing_subst bs  in subst_comp uu____4726 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___99_4783 = x  in
            let uu____4784 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___99_4783.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___99_4783.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4784
            }  in
          let s' =
            let uu____4790 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4790
             in
          let uu____4793 = aux s' tl1  in (x1, imp) :: uu____4793
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
        (fun uu____4819  ->
           let uu____4820 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4820)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4873 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4896 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4962  ->
                    fun uu____4963  ->
                      match (uu____4962, uu____4963) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5066 = aux sub2 p2  in
                          (match uu____5066 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4896 with
           | (pats1,sub2) ->
               ((let uu___100_5168 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___100_5168.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___101_5187 = x  in
            let uu____5188 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___101_5187.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___101_5187.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5188
            }  in
          let sub2 =
            let uu____5194 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5194
             in
          ((let uu___102_5202 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___102_5202.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___103_5207 = x  in
            let uu____5208 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_5207.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_5207.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5208
            }  in
          let sub2 =
            let uu____5214 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5214
             in
          ((let uu___104_5222 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___104_5222.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___105_5232 = x  in
            let uu____5233 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___105_5232.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___105_5232.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5233
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___106_5242 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___106_5242.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5251  ->
    match uu____5251 with
    | (p,wopt,e) ->
        let uu____5271 = close_pat p  in
        (match uu____5271 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5308 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5308
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
      let uu____5381 = univ_var_opening us  in
      match uu____5381 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5423 = univ_var_opening us  in
      match uu____5423 with
      | (s,us') -> let uu____5446 = subst_comp s c  in (us', uu____5446)
  
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
      let uu____5502 =
        let uu____5513 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5513
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5546  ->
                 match uu____5546 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5579 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5579  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___107_5585 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___107_5585.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___107_5585.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___107_5585.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___107_5585.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___107_5585.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___107_5585.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5502 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5623 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5651  ->
                             match uu____5651 with
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
                    match uu____5623 with
                    | (uu____5692,us,u_let_rec_opening) ->
                        let uu___108_5703 = lb  in
                        let uu____5704 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5707 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___108_5703.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5704;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___108_5703.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5707;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___108_5703.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___108_5703.FStar_Syntax_Syntax.lbpos)
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
      let uu____5733 =
        let uu____5740 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5740
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5762  ->
                 match uu____5762 with
                 | (i,out) ->
                     let uu____5781 =
                       let uu____5784 =
                         let uu____5785 =
                           let uu____5790 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5790, i)  in
                         FStar_Syntax_Syntax.NM uu____5785  in
                       uu____5784 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5781)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5733 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5822 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5840  ->
                             match uu____5840 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5822 with
                    | (uu____5863,u_let_rec_closing) ->
                        let uu___109_5869 = lb  in
                        let uu____5870 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5873 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___109_5869.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___109_5869.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5870;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___109_5869.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5873;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___109_5869.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___109_5869.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5888  ->
      match uu____5888 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5917  ->
                   match uu____5917 with
                   | (x,uu____5923) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5944  ->
      match uu____5944 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5970 = subst s t  in (us', uu____5970)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5988  ->
      match uu____5988 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6002 = subst s1 t  in (us, uu____6002)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6034  ->
              match uu____6034 with
              | (x,uu____6040) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun b  ->
    fun t  ->
      let uu____6060 = open_term [b] t  in
      match uu____6060 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6091 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6120 =
        let uu____6125 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6125 t  in
      match uu____6120 with
      | (bs,t1) ->
          let uu____6138 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6138, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6161 = open_term_bvs [bv] t  in
      match uu____6161 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6176 -> failwith "impossible: open_term_bv"
  