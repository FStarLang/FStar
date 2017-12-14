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
      fun uu___53_146  ->
        match uu___53_146 with
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
      | uu____424 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____449) ->
        let uu____474 = FStar_Syntax_Unionfind.find uv  in
        (match uu____474 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____480 -> t)
    | uu____483 -> t
  
let force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t  in
    let uu____496 = FStar_Util.physical_equality t t'  in
    if uu____496
    then t
    else
      delay t'
        ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
  
let rec force_delayed_thunk :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____563 = FStar_ST.op_Bang m  in
        (match uu____563 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t'  in
             (FStar_ST.op_Colon_Equals m (FStar_Pervasives_Native.Some t'1);
              t'1))
    | uu____723 -> t
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____736 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____736 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____740 -> u)
    | uu____743 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___54_760  ->
           match uu___54_760 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____765 =
                 let uu____766 =
                   let uu____767 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____767  in
                 FStar_Syntax_Syntax.bv_to_name uu____766  in
               FStar_Pervasives_Native.Some uu____765
           | uu____768 -> FStar_Pervasives_Native.None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___55_785  ->
           match uu___55_785 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____790 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___59_793 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___59_793.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___59_793.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____790
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____802 -> FStar_Pervasives_Native.None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___56_818  ->
           match uu___56_818 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____823 -> FStar_Pervasives_Native.None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___57_839  ->
           match uu___57_839 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____844 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____866 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____876 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____876
      | FStar_Syntax_Syntax.U_max us ->
          let uu____880 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____880
  
let tag_with_range :
  'Auu____886 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____886,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 =
            let uu____917 = FStar_Range.use_range r  in
            FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____917  in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____920 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                FStar_Syntax_Syntax.Tm_bvar uu____920
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____922 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                FStar_Syntax_Syntax.Tm_name uu____922
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___60_928 = fv.FStar_Syntax_Syntax.fv_name  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___60_928.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___61_930 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___61_930.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___61_930.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___62_932 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars = (uu___62_932.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____938 .
    FStar_Ident.lident ->
      ('Auu____938,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____962 =
            let uu____963 = FStar_Range.use_range r  in
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) uu____963
             in
          FStar_Ident.set_lid_range l uu____962
  
let mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' ->
          let uu____977 = FStar_Range.use_range r'  in
          FStar_Range.set_use_range r uu____977
  
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
      | uu____1080 ->
          let t0 = force_delayed_thunk t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1090 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1095 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1100 -> tag_with_range t0 s
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
               let uu____1209 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1210 =
                 let uu____1213 =
                   let uu____1214 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1214  in
                 FStar_Syntax_Syntax.mk uu____1213  in
               uu____1210 FStar_Pervasives_Native.None uu____1209
           | uu____1224 ->
               let uu____1225 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1225)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___58_1239  ->
              match uu___58_1239 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1243 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1243
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
      | uu____1277 ->
          let uu___63_1288 = t  in
          let uu____1289 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1296 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1301 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1304 =
            FStar_List.map
              (fun uu____1329  ->
                 match uu____1329 with
                 | (t1,imp) ->
                     let uu____1348 = subst' s t1  in (uu____1348, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1353 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1289;
            FStar_Syntax_Syntax.effect_name = uu____1296;
            FStar_Syntax_Syntax.result_typ = uu____1301;
            FStar_Syntax_Syntax.effect_args = uu____1304;
            FStar_Syntax_Syntax.flags = uu____1353
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
      | uu____1390 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1413 = subst' s t1  in
               let uu____1414 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1413 uu____1414
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1433 = subst' s t1  in
               let uu____1434 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1433 uu____1434
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1444 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1444)

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
      | FStar_Syntax_Syntax.NT uu____1459 -> s
  
let shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1475 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1475)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1475)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1502 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1502, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1518 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1518) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1518) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1534  ->
      match uu____1534 with
      | (x,imp) ->
          let uu____1541 =
            let uu___64_1542 = x  in
            let uu____1543 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___64_1542.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___64_1542.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1543
            }  in
          (uu____1541, imp)
  
let subst_binders' :
  'Auu____1549 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1549) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1549) FStar_Pervasives_Native.tuple2
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
                  (let uu____1609 = shift_subst' i s  in
                   subst_binder' uu____1609 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1635 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1635)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1635)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1655  ->
      match uu____1655 with
      | (t,imp) -> let uu____1668 = subst' s t  in (uu____1668, imp)
  
let subst_args' :
  'Auu____1675 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1675)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1675)
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
        | FStar_Syntax_Syntax.Pat_constant uu____1763 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1784 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1838  ->
                      fun uu____1839  ->
                        match (uu____1838, uu____1839) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1918 = aux n2 p2  in
                            (match uu____1918 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1784 with
             | (pats1,n2) ->
                 ((let uu___65_1976 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___65_1976.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___66_2002 = x  in
              let uu____2003 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___66_2002.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___66_2002.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2003
              }  in
            ((let uu___67_2009 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___67_2009.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___68_2025 = x  in
              let uu____2026 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___68_2025.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___68_2025.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2026
              }  in
            ((let uu___69_2032 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___69_2032.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___70_2053 = x  in
              let uu____2054 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___70_2053.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___70_2053.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2054
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___71_2063 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___71_2063.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
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
          let uu____2083 =
            let uu___72_2084 = rc  in
            let uu____2085 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___72_2084.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2085;
              FStar_Syntax_Syntax.residual_flags =
                (uu___72_2084.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2083
  
let push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2112 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2112  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2115 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2142 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2147 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2152 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2177 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2178 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2179 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2195 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2195 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2224 =
            let uu____2225 =
              let uu____2240 = subst' s t0  in
              let uu____2243 = subst_args' s args  in
              (uu____2240, uu____2243)  in
            FStar_Syntax_Syntax.Tm_app uu____2225  in
          mk1 uu____2224
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2338 = subst' s t1  in FStar_Util.Inl uu____2338
            | FStar_Util.Inr c ->
                let uu____2352 = subst_comp' s c  in
                FStar_Util.Inr uu____2352
             in
          let uu____2359 =
            let uu____2360 =
              let uu____2387 = subst' s t0  in
              let uu____2390 =
                let uu____2407 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2407)  in
              (uu____2387, uu____2390, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2360  in
          mk1 uu____2359
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2491 =
            let uu____2492 =
              let uu____2509 = subst_binders' s bs  in
              let uu____2516 = subst' s' body  in
              let uu____2519 = push_subst_lcomp s' lopt  in
              (uu____2509, uu____2516, uu____2519)  in
            FStar_Syntax_Syntax.Tm_abs uu____2492  in
          mk1 uu____2491
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2555 =
            let uu____2556 =
              let uu____2569 = subst_binders' s bs  in
              let uu____2576 =
                let uu____2579 = shift_subst' n1 s  in
                subst_comp' uu____2579 comp  in
              (uu____2569, uu____2576)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2556  in
          mk1 uu____2555
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___73_2611 = x  in
            let uu____2612 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___73_2611.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___73_2611.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2612
            }  in
          let phi1 =
            let uu____2618 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2618 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2745  ->
                    match uu____2745 with
                    | (pat,wopt,branch) ->
                        let uu____2791 = subst_pat' s pat  in
                        (match uu____2791 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2839 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____2839
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
                      let uu____2924 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____2924
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___74_2939 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___74_2939.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___74_2939.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___75_2941 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___75_2941.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___75_2941.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2968 =
            let uu____2969 =
              let uu____2976 = subst' s t0  in
              let uu____2979 =
                let uu____2980 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____2980  in
              (uu____2976, uu____2979)  in
            FStar_Syntax_Syntax.Tm_meta uu____2969  in
          mk1 uu____2968
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3040 =
            let uu____3041 =
              let uu____3048 = subst' s t0  in
              let uu____3051 =
                let uu____3052 =
                  let uu____3059 = subst' s t1  in (m, uu____3059)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3052  in
              (uu____3048, uu____3051)  in
            FStar_Syntax_Syntax.Tm_meta uu____3041  in
          mk1 uu____3040
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3078 =
            let uu____3079 =
              let uu____3086 = subst' s t0  in
              let uu____3089 =
                let uu____3090 =
                  let uu____3099 = subst' s t1  in (m1, m2, uu____3099)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3090  in
              (uu____3086, uu____3089)  in
            FStar_Syntax_Syntax.Tm_meta uu____3079  in
          mk1 uu____3078
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3112 =
            let uu____3113 = let uu____3120 = subst' s t1  in (uu____3120, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3113  in
          mk1 uu____3112
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3183 = push_subst s t2  in compress uu____3183  in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3203 ->
        let t' = force_uvar t1  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3207 -> compress t'
         | uu____3232 -> t')
  
let subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      let uu____3259 =
        let uu____3260 =
          let uu____3263 =
            let uu____3264 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3264  in
          FStar_Pervasives_Native.Some uu____3263  in
        ([], uu____3260)  in
      subst' uu____3259 t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3298 =
      FStar_List.fold_right
        (fun uu____3321  ->
           fun uu____3322  ->
             match (uu____3321, uu____3322) with
             | ((x,uu____3350),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3298 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3383 .
    (FStar_Syntax_Syntax.bv,'Auu____3383) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3383) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___76_3489 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3490 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___76_3489.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___76_3489.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3490
            }  in
          let o1 =
            let uu____3496 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3496
             in
          let uu____3499 = aux bs' o1  in
          (match uu____3499 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let open_binders : FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3557 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3557
  
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3590 = open_binders' bs  in
      match uu____3590 with
      | (bs',opening) ->
          let uu____3627 = subst opening t  in (bs', uu____3627, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3646 = open_term' bs t  in
      match uu____3646 with | (b,t1,uu____3659) -> (b, t1)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3670 = open_binders' bs  in
      match uu____3670 with
      | (bs',opening) ->
          let uu____3705 = subst_comp opening t  in (bs', uu____3705)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3785 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3814 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3906  ->
                    fun uu____3907  ->
                      match (uu____3906, uu____3907) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____4055 = open_pat_aux sub2 renaming1 p2  in
                          (match uu____4055 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming))
             in
          (match uu____3814 with
           | (pats1,sub2,renaming1) ->
               ((let uu___77_4225 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___77_4225.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___78_4244 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4245 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___78_4244.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___78_4244.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4245
            }  in
          let sub2 =
            let uu____4251 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4251
             in
          ((let uu___79_4265 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___79_4265.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___80_4274 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4275 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___80_4274.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___80_4274.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4275
            }  in
          let sub2 =
            let uu____4281 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4281
             in
          ((let uu___81_4295 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___81_4295.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___82_4309 = x  in
            let uu____4310 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___82_4309.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___82_4309.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4310
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___83_4325 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___83_4325.FStar_Syntax_Syntax.p)
            }), sub1, renaming)
       in
    let uu____4328 = open_pat_aux [] [] p  in
    match uu____4328 with | (p1,sub1,uu____4355) -> (p1, sub1)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4382  ->
    match uu____4382 with
    | (p,wopt,e) ->
        let uu____4402 = open_pat p  in
        (match uu____4402 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4421 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4421
                in
             let e1 = subst opening e  in (p1, wopt1, e1))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4431 = closing_subst bs  in subst uu____4431 t
  
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4440 = closing_subst bs  in subst_comp uu____4440 c
  
let close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___84_4491 = x  in
            let uu____4492 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___84_4491.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___84_4491.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4492
            }  in
          let s' =
            let uu____4498 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4498
             in
          let uu____4501 = aux s' tl1  in (x1, imp) :: uu____4501
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___85_4521 = lc  in
      let uu____4522 = subst s lc.FStar_Syntax_Syntax.res_typ  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___85_4521.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4522;
        FStar_Syntax_Syntax.cflags =
          (uu___85_4521.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4527  ->
             let uu____4528 = lc.FStar_Syntax_Syntax.comp ()  in
             subst_comp s uu____4528)
      }
  
let close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4575 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4598 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4664  ->
                    fun uu____4665  ->
                      match (uu____4664, uu____4665) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4768 = aux sub2 p2  in
                          (match uu____4768 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4598 with
           | (pats1,sub2) ->
               ((let uu___86_4870 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___86_4870.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___87_4889 = x  in
            let uu____4890 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___87_4889.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___87_4889.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4890
            }  in
          let sub2 =
            let uu____4896 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4896
             in
          ((let uu___88_4904 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___88_4904.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___89_4909 = x  in
            let uu____4910 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___89_4909.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___89_4909.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4910
            }  in
          let sub2 =
            let uu____4916 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4916
             in
          ((let uu___90_4924 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___90_4924.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___91_4934 = x  in
            let uu____4935 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___91_4934.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___91_4934.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4935
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___92_4944 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___92_4944.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4949  ->
    match uu____4949 with
    | (p,wopt,e) ->
        let uu____4969 = close_pat p  in
        (match uu____4969 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5000 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5000
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
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
  
let univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
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
      let uu____5055 = univ_var_opening us  in
      match uu____5055 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5095 = univ_var_opening us  in
      match uu____5095 with
      | (s,us') -> let uu____5118 = subst_comp s c  in (us', uu____5118)
  
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
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
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
      let uu____5162 =
        let uu____5173 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5173
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5206  ->
                 match uu____5206 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5239 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5239  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___93_5245 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___93_5245.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___93_5245.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___93_5245.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___93_5245.FStar_Syntax_Syntax.lbdef)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5162 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5283 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5311  ->
                             match uu____5311 with
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
                    match uu____5283 with
                    | (uu____5352,us,u_let_rec_opening) ->
                        let uu___94_5363 = lb  in
                        let uu____5364 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5367 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___94_5363.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5364;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___94_5363.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5367
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
      let uu____5389 =
        let uu____5396 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5396
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5418  ->
                 match uu____5418 with
                 | (i,out) ->
                     let uu____5437 =
                       let uu____5440 =
                         let uu____5441 =
                           let uu____5446 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5446, i)  in
                         FStar_Syntax_Syntax.NM uu____5441  in
                       uu____5440 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5437)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5389 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5478 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5496  ->
                             match uu____5496 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5478 with
                    | (uu____5519,u_let_rec_closing) ->
                        let uu___95_5525 = lb  in
                        let uu____5526 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5529 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___95_5525.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___95_5525.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5526;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___95_5525.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5529
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5540  ->
      match uu____5540 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5565  ->
                   match uu____5565 with
                   | (x,uu____5571) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5586  ->
      match uu____5586 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5608 = subst s t  in (us', uu____5608)
  
let subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun s  ->
    fun uu____5618  ->
      match uu____5618 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5628 = subst s1 t  in (us, uu____5628)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5650  ->
              match uu____5650 with
              | (x,uu____5656) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs 