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
      fun uu___65_164  ->
        match uu___65_164 with
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
        let uu____521 = FStar_Syntax_Unionfind.find uv  in
        (match uu____521 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____531 =
               let uu____534 =
                 let uu____541 = delay t' s  in force_uvar' uu____541  in
               FStar_Pervasives_Native.fst uu____534  in
             (uu____531, true)
         | uu____548 -> (t, false))
    | uu____553 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____569 = force_uvar' t  in
    match uu____569 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____591 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____591, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____663 = FStar_ST.op_Bang m  in
        (match uu____663 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____736 = try_read_memo_aux t'  in
             (match uu____736 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____814 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____828 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____828
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____851 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____851 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____855 -> u)
    | uu____858 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___66_879  ->
           match uu___66_879 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____884 =
                 let uu____885 =
                   let uu____886 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____886  in
                 FStar_Syntax_Syntax.bv_to_name uu____885  in
               FStar_Pervasives_Native.Some uu____884
           | uu____887 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___67_912  ->
           match uu___67_912 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____919 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___73_924 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___73_924.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___73_924.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____919
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____935 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___68_957  ->
           match uu___68_957 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____962 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___69_982  ->
           match uu___69_982 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____987 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1013 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1023 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1023
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1027 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1027
  
let tag_with_range :
  'Auu____1036 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1036,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____1069 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1069
             in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____1072 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_bvar uu____1072
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____1074 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_name uu____1074
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___74_1080 = fv.FStar_Syntax_Syntax.fv_name  in
                  let uu____1081 = FStar_Ident.set_lid_range l r1  in
                  {
                    FStar_Syntax_Syntax.v = uu____1081;
                    FStar_Syntax_Syntax.p =
                      (uu___74_1080.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___75_1083 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___75_1083.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___75_1083.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___76_1085 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___76_1085.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____1094 .
    FStar_Ident.lident ->
      ('Auu____1094,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1120 =
            let uu____1121 = FStar_Ident.range_of_lid l  in
            let uu____1122 = FStar_Range.use_range r  in
            FStar_Range.set_use_range uu____1121 uu____1122  in
          FStar_Ident.set_lid_range l uu____1120
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1140 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____1140
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1252 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1260 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1265 -> tag_with_range t0 s
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
               let uu____1344 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1345 =
                 let uu____1352 =
                   let uu____1353 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1353  in
                 FStar_Syntax_Syntax.mk uu____1352  in
               uu____1345 FStar_Pervasives_Native.None uu____1344
           | uu____1363 ->
               let uu____1364 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1364)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___70_1376  ->
              match uu___70_1376 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1380 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1380
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
      | uu____1414 ->
          let uu___77_1425 = t  in
          let uu____1426 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1433 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1438 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1441 =
            FStar_List.map
              (fun uu____1462  ->
                 match uu____1462 with
                 | (t1,imp) ->
                     let uu____1473 = subst' s t1  in (uu____1473, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1474 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1426;
            FStar_Syntax_Syntax.effect_name = uu____1433;
            FStar_Syntax_Syntax.result_typ = uu____1438;
            FStar_Syntax_Syntax.effect_args = uu____1441;
            FStar_Syntax_Syntax.flags = uu____1474
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
      | uu____1511 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1534 = subst' s t1  in
               let uu____1535 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1534 uu____1535
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1554 = subst' s t1  in
               let uu____1555 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1554 uu____1555
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1565 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1565)

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
      | FStar_Syntax_Syntax.NT uu____1584 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1607 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1607)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1607)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1636 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1636, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1655 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1655) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1655) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1673  ->
      match uu____1673 with
      | (x,imp) ->
          let uu____1680 =
            let uu___78_1681 = x  in
            let uu____1682 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___78_1681.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___78_1681.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1682
            }  in
          (uu____1680, imp)
  
let subst_binders' :
  'Auu____1691 .
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____1691) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1691) FStar_Pervasives_Native.tuple2
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
                  (let uu____1773 = shift_subst' i s  in
                   subst_binder' uu____1773 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1806 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1806) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1806)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1824  ->
      match uu____1824 with
      | (t,imp) -> let uu____1831 = subst' s t  in (uu____1831, imp)
  
let subst_args' :
  'Auu____1837 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1837) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1837)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1928 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1947 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2001  ->
                      fun uu____2002  ->
                        match (uu____2001, uu____2002) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2081 = aux n2 p2  in
                            (match uu____2081 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1947 with
             | (pats1,n2) ->
                 ((let uu___79_2137 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___79_2137.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___80_2167 = x  in
              let uu____2168 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___80_2167.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___80_2167.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2168
              }  in
            ((let uu___81_2172 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___81_2172.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___82_2188 = x  in
              let uu____2189 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___82_2188.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___82_2188.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2189
              }  in
            ((let uu___83_2193 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___83_2193.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___84_2214 = x  in
              let uu____2215 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___84_2214.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___84_2214.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2215
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___85_2220 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___85_2220.FStar_Syntax_Syntax.p)
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
          let uu____2244 =
            let uu___86_2245 = rc  in
            let uu____2246 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___86_2245.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2246;
              FStar_Syntax_Syntax.residual_flags =
                (uu___86_2245.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2244
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____2289  ->
                  match uu____2289 with
                  | (x',uu____2295) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___72_2307 =
          match uu___72_2307 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___71_2338  ->
                        match uu___71_2338 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2347 = should_retain x  in
                            if uu____2347
                            then
                              let uu____2350 =
                                let uu____2351 =
                                  let uu____2358 =
                                    delay t
                                      (rest, FStar_Pervasives_Native.None)
                                     in
                                  (x, uu____2358)  in
                                FStar_Syntax_Syntax.NT uu____2351  in
                              [uu____2350]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2372 = should_retain x  in
                            if uu____2372
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___87_2378 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___87_2378.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___87_2378.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Pervasives_Native.None)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____2389 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2393 -> []))
                 in
              let uu____2394 = aux rest  in FStar_List.append hd1 uu____2394
           in
        let uu____2397 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2397 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2471 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2471  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2474 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2502 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2507 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2538 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2538 with
           | FStar_Pervasives_Native.None  ->
               let uu____2543 =
                 let uu___88_2546 = t  in
                 let uu____2549 =
                   let uu____2550 =
                     let uu____2565 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2565)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2550  in
                 {
                   FStar_Syntax_Syntax.n = uu____2549;
                   FStar_Syntax_Syntax.pos =
                     (uu___88_2546.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___88_2546.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2543 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2593 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2594 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2595 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2611 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2611 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2640 =
            let uu____2641 =
              let uu____2656 = subst' s t0  in
              let uu____2659 = subst_args' s args  in
              (uu____2656, uu____2659)  in
            FStar_Syntax_Syntax.Tm_app uu____2641  in
          mk1 uu____2640
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2754 = subst' s t1  in FStar_Util.Inl uu____2754
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
            let uu___89_3023 = x  in
            let uu____3024 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___89_3023.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___89_3023.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3024
            }  in
          let phi1 =
            let uu____3028 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3028 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3145  ->
                    match uu____3145 with
                    | (pat,wopt,branch) ->
                        let uu____3175 = subst_pat' s pat  in
                        (match uu____3175 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3207 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3207
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
                      let uu____3280 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3280
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___90_3295 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___90_3295.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___90_3295.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___91_3297 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___91_3297.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___91_3297.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___91_3297.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___91_3297.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3324 =
            let uu____3325 =
              let uu____3332 = subst' s t0  in
              let uu____3335 =
                let uu____3336 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3336  in
              (uu____3332, uu____3335)  in
            FStar_Syntax_Syntax.Tm_meta uu____3325  in
          mk1 uu____3324
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3390 =
            let uu____3391 =
              let uu____3398 = subst' s t0  in
              let uu____3401 =
                let uu____3402 =
                  let uu____3409 = subst' s t1  in (m, uu____3409)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3402  in
              (uu____3398, uu____3401)  in
            FStar_Syntax_Syntax.Tm_meta uu____3391  in
          mk1 uu____3390
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3428 =
            let uu____3429 =
              let uu____3436 = subst' s t0  in
              let uu____3439 =
                let uu____3440 =
                  let uu____3449 = subst' s t1  in (m1, m2, uu____3449)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3440  in
              (uu____3436, uu____3439)  in
            FStar_Syntax_Syntax.Tm_meta uu____3429  in
          mk1 uu____3428
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3464 =
                 let uu____3465 =
                   let uu____3472 = subst' s tm  in (uu____3472, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3465  in
               mk1 uu____3464
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3486 =
            let uu____3487 = let uu____3494 = subst' s t1  in (uu____3494, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3487  in
          mk1 uu____3486
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3507 = force_uvar t1  in
    match uu____3507 with
    | (t2,uu____3513) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3566 =
                 let uu____3571 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3571  in
               FStar_ST.op_Colon_Equals memo uu____3566);
              compress t2)
         | uu____3629 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3664 =
        let uu____3665 =
          let uu____3668 =
            let uu____3669 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3669  in
          FStar_Pervasives_Native.Some uu____3668  in
        ([], uu____3665)  in
      subst' uu____3664 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3709 =
      FStar_List.fold_right
        (fun uu____3732  ->
           fun uu____3733  ->
             match (uu____3732, uu____3733) with
             | ((x,uu____3761),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3709 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3796 .
    (FStar_Syntax_Syntax.bv,'Auu____3796) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3796) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___92_3907 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3908 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___92_3907.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___92_3907.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3908
            }  in
          let o1 =
            let uu____3914 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3914
             in
          let uu____3917 = aux bs' o1  in
          (match uu____3917 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3977 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3977
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4014 = open_binders' bs  in
      match uu____4014 with
      | (bs',opening) ->
          let uu____4051 = subst opening t  in (bs', uu____4051, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4066 = open_term' bs t  in
      match uu____4066 with | (b,t1,uu____4079) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4094 = open_binders' bs  in
      match uu____4094 with
      | (bs',opening) ->
          let uu____4129 = subst_comp opening t  in (bs', uu____4129)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4178 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4201 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4267  ->
                    fun uu____4268  ->
                      match (uu____4267, uu____4268) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4371 = open_pat_aux sub2 p2  in
                          (match uu____4371 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4201 with
           | (pats1,sub2) ->
               ((let uu___93_4473 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___93_4473.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___94_4492 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4493 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___94_4492.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___94_4492.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4493
            }  in
          let sub2 =
            let uu____4499 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4499
             in
          ((let uu___95_4507 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___95_4507.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___96_4512 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4513 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___96_4512.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___96_4512.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4513
            }  in
          let sub2 =
            let uu____4519 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4519
             in
          ((let uu___97_4527 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___97_4527.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___98_4537 = x  in
            let uu____4538 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___98_4537.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___98_4537.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4538
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___99_4547 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___99_4547.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4560  ->
    match uu____4560 with
    | (p,wopt,e) ->
        let uu____4584 = open_pat p  in
        (match uu____4584 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4613 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4613
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4628 = open_branch' br  in
    match uu____4628 with | (br1,uu____4634) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4645 = closing_subst bs  in subst uu____4645 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4658 = closing_subst bs  in subst_comp uu____4658 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___100_4715 = x  in
            let uu____4716 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___100_4715.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___100_4715.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4716
            }  in
          let s' =
            let uu____4722 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4722
             in
          let uu____4725 = aux s' tl1  in (x1, imp) :: uu____4725
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
        (fun uu____4751  ->
           let uu____4752 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4752)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4805 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4828 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4894  ->
                    fun uu____4895  ->
                      match (uu____4894, uu____4895) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4998 = aux sub2 p2  in
                          (match uu____4998 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4828 with
           | (pats1,sub2) ->
               ((let uu___101_5100 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___101_5100.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___102_5119 = x  in
            let uu____5120 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___102_5119.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___102_5119.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5120
            }  in
          let sub2 =
            let uu____5126 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5126
             in
          ((let uu___103_5134 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___103_5134.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___104_5139 = x  in
            let uu____5140 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_5139.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_5139.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5140
            }  in
          let sub2 =
            let uu____5146 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5146
             in
          ((let uu___105_5154 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___105_5154.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___106_5164 = x  in
            let uu____5165 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_5164.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_5164.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5165
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___107_5174 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___107_5174.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5183  ->
    match uu____5183 with
    | (p,wopt,e) ->
        let uu____5203 = close_pat p  in
        (match uu____5203 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5240 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5240
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
      let uu____5313 = univ_var_opening us  in
      match uu____5313 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5355 = univ_var_opening us  in
      match uu____5355 with
      | (s,us') -> let uu____5378 = subst_comp s c  in (us', uu____5378)
  
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
      let uu____5434 =
        let uu____5445 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5445
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5478  ->
                 match uu____5478 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5511 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5511  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___108_5517 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___108_5517.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___108_5517.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___108_5517.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___108_5517.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___108_5517.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___108_5517.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5434 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5555 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5583  ->
                             match uu____5583 with
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
                    match uu____5555 with
                    | (uu____5624,us,u_let_rec_opening) ->
                        let uu___109_5635 = lb  in
                        let uu____5636 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5639 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___109_5635.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5636;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___109_5635.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5639;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___109_5635.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___109_5635.FStar_Syntax_Syntax.lbpos)
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
      let uu____5665 =
        let uu____5672 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5672
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5694  ->
                 match uu____5694 with
                 | (i,out) ->
                     let uu____5713 =
                       let uu____5716 =
                         let uu____5717 =
                           let uu____5722 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5722, i)  in
                         FStar_Syntax_Syntax.NM uu____5717  in
                       uu____5716 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5713)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5665 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5754 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5772  ->
                             match uu____5772 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5754 with
                    | (uu____5795,u_let_rec_closing) ->
                        let uu___110_5801 = lb  in
                        let uu____5802 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5805 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___110_5801.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___110_5801.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5802;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___110_5801.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5805;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___110_5801.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___110_5801.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5820  ->
      match uu____5820 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5849  ->
                   match uu____5849 with
                   | (x,uu____5855) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5876  ->
      match uu____5876 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5902 = subst s t  in (us', uu____5902)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5920  ->
      match uu____5920 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5934 = subst s1 t  in (us, uu____5934)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5966  ->
              match uu____5966 with
              | (x,uu____5972) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____5992 = open_term [b] t  in
      match uu____5992 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6023 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6052 =
        let uu____6057 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6057 t  in
      match uu____6052 with
      | (bs,t1) ->
          let uu____6070 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6070, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6093 = open_term_bvs [bv] t  in
      match uu____6093 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6108 -> failwith "impossible: open_term_bv"
  