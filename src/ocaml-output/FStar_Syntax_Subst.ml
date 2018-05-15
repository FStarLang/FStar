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
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____571 = force_uvar' t  in
    match uu____571 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____599 =
             delay t'
               ([],
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____599, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____675 = FStar_ST.op_Bang m  in
        (match uu____675 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____748 = try_read_memo_aux t'  in
             (match uu____748 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____826 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____840 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____840
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____863 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____863 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____867 -> u)
    | uu____870 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___66_891  ->
           match uu___66_891 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____896 =
                 let uu____897 =
                   let uu____898 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____898  in
                 FStar_Syntax_Syntax.bv_to_name uu____897  in
               FStar_Pervasives_Native.Some uu____896
           | uu____899 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___67_924  ->
           match uu___67_924 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____931 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___73_936 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___73_936.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___73_936.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____931
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____947 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___68_969  ->
           match uu___68_969 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____974 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___69_994  ->
           match uu___69_994 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____999 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1025 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1035 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1035
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1039 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1039
  
let tag_with_range :
  'Auu____1048 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1048,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____1081 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1081
             in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____1084 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_bvar uu____1084
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____1086 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                   in
                FStar_Syntax_Syntax.Tm_name uu____1086
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___74_1092 = fv.FStar_Syntax_Syntax.fv_name  in
                  let uu____1093 = FStar_Ident.set_lid_range l r1  in
                  {
                    FStar_Syntax_Syntax.v = uu____1093;
                    FStar_Syntax_Syntax.p =
                      (uu___74_1092.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___75_1095 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___75_1095.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___75_1095.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___76_1097 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___76_1097.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____1106 .
    FStar_Ident.lident ->
      ('Auu____1106,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____1132 =
            let uu____1133 = FStar_Ident.range_of_lid l  in
            let uu____1134 = FStar_Range.use_range r  in
            FStar_Range.set_use_range uu____1133 uu____1134  in
          FStar_Ident.set_lid_range l uu____1132
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____1152 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____1152
  
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
      | uu____1264 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1272 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1277 -> tag_with_range t0 s
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
           (fun uu___70_1388  ->
              match uu___70_1388 with
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
          let uu___77_1437 = t  in
          let uu____1438 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1445 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1450 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1453 =
            FStar_List.map
              (fun uu____1474  ->
                 match uu____1474 with
                 | (t1,imp) ->
                     let uu____1485 = subst' s t1  in (uu____1485, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1486 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1438;
            FStar_Syntax_Syntax.effect_name = uu____1445;
            FStar_Syntax_Syntax.result_typ = uu____1450;
            FStar_Syntax_Syntax.effect_args = uu____1453;
            FStar_Syntax_Syntax.flags = uu____1486
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
      | uu____1523 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1546 = subst' s t1  in
               let uu____1547 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1546 uu____1547
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1566 = subst' s t1  in
               let uu____1567 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1566 uu____1567
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1577 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1577)

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
      | FStar_Syntax_Syntax.NT uu____1596 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1619 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1619)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1619)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1648 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1648, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1667 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1667) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1667) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1685  ->
      match uu____1685 with
      | (x,imp) ->
          let uu____1692 =
            let uu___78_1693 = x  in
            let uu____1694 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___78_1693.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___78_1693.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1694
            }  in
          (uu____1692, imp)
  
let subst_binders' :
  'Auu____1703 .
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____1703) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1703) FStar_Pervasives_Native.tuple2
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
                  (let uu____1785 = shift_subst' i s  in
                   subst_binder' uu____1785 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1818 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1818) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1818)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1836  ->
      match uu____1836 with
      | (t,imp) -> let uu____1843 = subst' s t  in (uu____1843, imp)
  
let subst_args' :
  'Auu____1849 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1849) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1849)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1940 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1959 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2013  ->
                      fun uu____2014  ->
                        match (uu____2013, uu____2014) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2093 = aux n2 p2  in
                            (match uu____2093 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1959 with
             | (pats1,n2) ->
                 ((let uu___79_2149 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___79_2149.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___80_2177 = x  in
              let uu____2178 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___80_2177.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___80_2177.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2178
              }  in
            ((let uu___81_2182 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___81_2182.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___82_2198 = x  in
              let uu____2199 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___82_2198.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___82_2198.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2199
              }  in
            ((let uu___83_2203 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___83_2203.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___84_2224 = x  in
              let uu____2225 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___84_2224.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___84_2224.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2225
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___85_2230 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___85_2230.FStar_Syntax_Syntax.p)
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
          let uu____2254 =
            let uu___86_2255 = rc  in
            let uu____2256 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___86_2255.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2256;
              FStar_Syntax_Syntax.residual_flags =
                (uu___86_2255.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2254
  
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
               (fun uu____2299  ->
                  match uu____2299 with
                  | (x',uu____2305) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___72_2317 =
          match uu___72_2317 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___71_2348  ->
                        match uu___71_2348 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2357 = should_retain x  in
                            if uu____2357
                            then
                              let uu____2360 =
                                let uu____2361 =
                                  let uu____2368 =
                                    delay t
                                      (rest, FStar_Pervasives_Native.None)
                                     in
                                  (x, uu____2368)  in
                                FStar_Syntax_Syntax.NT uu____2361  in
                              [uu____2360]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2382 = should_retain x  in
                            if uu____2382
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___87_2388 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___87_2388.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___87_2388.FStar_Syntax_Syntax.sort)
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
                               | uu____2399 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2403 -> []))
                 in
              let uu____2404 = aux rest  in FStar_List.append hd1 uu____2404
           in
        let uu____2407 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2407 with
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
        let uu____2481 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2481  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2484 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2512 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2517 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2548 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2548 with
           | FStar_Pervasives_Native.None  ->
               let uu____2553 =
                 let uu___88_2556 = t  in
                 let uu____2559 =
                   let uu____2560 =
                     let uu____2575 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2575)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2560  in
                 {
                   FStar_Syntax_Syntax.n = uu____2559;
                   FStar_Syntax_Syntax.pos =
                     (uu___88_2556.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___88_2556.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2553 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2603 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2604 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2605 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2621 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2621 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2650 =
            let uu____2651 =
              let uu____2666 = subst' s t0  in
              let uu____2669 = subst_args' s args  in
              (uu____2666, uu____2669)  in
            FStar_Syntax_Syntax.Tm_app uu____2651  in
          mk1 uu____2650
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2764 = subst' s t1  in FStar_Util.Inl uu____2764
            | FStar_Util.Inr c ->
                let uu____2778 = subst_comp' s c  in
                FStar_Util.Inr uu____2778
             in
          let uu____2785 =
            let uu____2786 =
              let uu____2813 = subst' s t0  in
              let uu____2816 =
                let uu____2833 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2833)  in
              (uu____2813, uu____2816, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2786  in
          mk1 uu____2785
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2917 =
            let uu____2918 =
              let uu____2935 = subst_binders' s bs  in
              let uu____2942 = subst' s' body  in
              let uu____2945 = push_subst_lcomp s' lopt  in
              (uu____2935, uu____2942, uu____2945)  in
            FStar_Syntax_Syntax.Tm_abs uu____2918  in
          mk1 uu____2917
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2981 =
            let uu____2982 =
              let uu____2995 = subst_binders' s bs  in
              let uu____3002 =
                let uu____3005 = shift_subst' n1 s  in
                subst_comp' uu____3005 comp  in
              (uu____2995, uu____3002)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2982  in
          mk1 uu____2981
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___89_3037 = x  in
            let uu____3038 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___89_3037.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___89_3037.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3038
            }  in
          let phi1 =
            let uu____3042 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3042 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3159  ->
                    match uu____3159 with
                    | (pat,wopt,branch) ->
                        let uu____3189 = subst_pat' s pat  in
                        (match uu____3189 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3221 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3221
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
                      let uu____3294 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3294
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___90_3309 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___90_3309.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___90_3309.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___91_3311 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___91_3311.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___91_3311.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___91_3311.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___91_3311.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3338 =
            let uu____3339 =
              let uu____3346 = subst' s t0  in
              let uu____3349 =
                let uu____3350 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3350  in
              (uu____3346, uu____3349)  in
            FStar_Syntax_Syntax.Tm_meta uu____3339  in
          mk1 uu____3338
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3404 =
            let uu____3405 =
              let uu____3412 = subst' s t0  in
              let uu____3415 =
                let uu____3416 =
                  let uu____3423 = subst' s t1  in (m, uu____3423)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3416  in
              (uu____3412, uu____3415)  in
            FStar_Syntax_Syntax.Tm_meta uu____3405  in
          mk1 uu____3404
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3442 =
            let uu____3443 =
              let uu____3450 = subst' s t0  in
              let uu____3453 =
                let uu____3454 =
                  let uu____3463 = subst' s t1  in (m1, m2, uu____3463)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3454  in
              (uu____3450, uu____3453)  in
            FStar_Syntax_Syntax.Tm_meta uu____3443  in
          mk1 uu____3442
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3478 =
                 let uu____3479 =
                   let uu____3486 = subst' s tm  in (uu____3486, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3479  in
               mk1 uu____3478
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3500 =
            let uu____3501 = let uu____3508 = subst' s t1  in (uu____3508, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3501  in
          mk1 uu____3500
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3521 = force_uvar t1  in
    match uu____3521 with
    | (t2,uu____3529) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3586 =
                 let uu____3591 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3591  in
               FStar_ST.op_Colon_Equals memo uu____3586);
              compress t2)
         | uu____3649 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3684 =
        let uu____3685 =
          let uu____3688 =
            let uu____3689 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3689  in
          FStar_Pervasives_Native.Some uu____3688  in
        ([], uu____3685)  in
      subst' uu____3684 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3729 =
      FStar_List.fold_right
        (fun uu____3752  ->
           fun uu____3753  ->
             match (uu____3752, uu____3753) with
             | ((x,uu____3781),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3729 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3816 .
    (FStar_Syntax_Syntax.bv,'Auu____3816) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3816) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___92_3927 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3928 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___92_3927.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___92_3927.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3928
            }  in
          let o1 =
            let uu____3934 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3934
             in
          let uu____3937 = aux bs' o1  in
          (match uu____3937 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3997 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3997
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____4034 = open_binders' bs  in
      match uu____4034 with
      | (bs',opening) ->
          let uu____4071 = subst opening t  in (bs', uu____4071, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4086 = open_term' bs t  in
      match uu____4086 with | (b,t1,uu____4099) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____4114 = open_binders' bs  in
      match uu____4114 with
      | (bs',opening) ->
          let uu____4149 = subst_comp opening t  in (bs', uu____4149)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4198 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4221 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4287  ->
                    fun uu____4288  ->
                      match (uu____4287, uu____4288) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4391 = open_pat_aux sub2 p2  in
                          (match uu____4391 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4221 with
           | (pats1,sub2) ->
               ((let uu___93_4493 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___93_4493.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___94_4512 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4513 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___94_4512.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___94_4512.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4513
            }  in
          let sub2 =
            let uu____4519 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4519
             in
          ((let uu___95_4527 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___95_4527.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___96_4532 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4533 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___96_4532.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___96_4532.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4533
            }  in
          let sub2 =
            let uu____4539 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4539
             in
          ((let uu___97_4547 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___97_4547.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___98_4557 = x  in
            let uu____4558 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___98_4557.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___98_4557.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4558
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___99_4567 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___99_4567.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4580  ->
    match uu____4580 with
    | (p,wopt,e) ->
        let uu____4604 = open_pat p  in
        (match uu____4604 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4633 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4633
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4652 = open_branch' br  in
    match uu____4652 with | (br1,uu____4658) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4669 = closing_subst bs  in subst uu____4669 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4682 = closing_subst bs  in subst_comp uu____4682 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___100_4739 = x  in
            let uu____4740 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___100_4739.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___100_4739.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4740
            }  in
          let s' =
            let uu____4746 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4746
             in
          let uu____4749 = aux s' tl1  in (x1, imp) :: uu____4749
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
        (fun uu____4775  ->
           let uu____4776 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4776)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4829 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4852 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4918  ->
                    fun uu____4919  ->
                      match (uu____4918, uu____4919) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5022 = aux sub2 p2  in
                          (match uu____5022 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4852 with
           | (pats1,sub2) ->
               ((let uu___101_5124 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___101_5124.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___102_5143 = x  in
            let uu____5144 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___102_5143.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___102_5143.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5144
            }  in
          let sub2 =
            let uu____5150 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5150
             in
          ((let uu___103_5158 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___103_5158.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___104_5163 = x  in
            let uu____5164 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___104_5163.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___104_5163.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5164
            }  in
          let sub2 =
            let uu____5170 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5170
             in
          ((let uu___105_5178 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___105_5178.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___106_5188 = x  in
            let uu____5189 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_5188.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_5188.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5189
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___107_5198 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___107_5198.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5207  ->
    match uu____5207 with
    | (p,wopt,e) ->
        let uu____5227 = close_pat p  in
        (match uu____5227 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5264 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5264
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
      let uu____5341 = univ_var_opening us  in
      match uu____5341 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5383 = univ_var_opening us  in
      match uu____5383 with
      | (s,us') -> let uu____5406 = subst_comp s c  in (us', uu____5406)
  
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
      let uu____5462 =
        let uu____5473 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5473
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5506  ->
                 match uu____5506 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5539 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5539  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___108_5545 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___108_5545.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___108_5545.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___108_5545.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___108_5545.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___108_5545.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___108_5545.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5462 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5583 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5611  ->
                             match uu____5611 with
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
                    match uu____5583 with
                    | (uu____5652,us,u_let_rec_opening) ->
                        let uu___109_5663 = lb  in
                        let uu____5664 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5667 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___109_5663.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5664;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___109_5663.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5667;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___109_5663.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___109_5663.FStar_Syntax_Syntax.lbpos)
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
      let uu____5693 =
        let uu____5700 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5700
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5722  ->
                 match uu____5722 with
                 | (i,out) ->
                     let uu____5741 =
                       let uu____5744 =
                         let uu____5745 =
                           let uu____5750 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5750, i)  in
                         FStar_Syntax_Syntax.NM uu____5745  in
                       uu____5744 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5741)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5693 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5782 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5800  ->
                             match uu____5800 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5782 with
                    | (uu____5823,u_let_rec_closing) ->
                        let uu___110_5829 = lb  in
                        let uu____5830 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5833 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___110_5829.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___110_5829.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5830;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___110_5829.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5833;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___110_5829.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___110_5829.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5848  ->
      match uu____5848 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5877  ->
                   match uu____5877 with
                   | (x,uu____5883) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5904  ->
      match uu____5904 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5930 = subst s t  in (us', uu____5930)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5948  ->
      match uu____5948 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5962 = subst s1 t  in (us, uu____5962)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5994  ->
              match uu____5994 with
              | (x,uu____6000) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6020 = open_term [b] t  in
      match uu____6020 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6051 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____6080 =
        let uu____6085 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6085 t  in
      match uu____6080 with
      | (bs,t1) ->
          let uu____6098 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6098, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____6121 = open_term_bvs [bv] t  in
      match uu____6121 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6136 -> failwith "impossible: open_term_bv"
  