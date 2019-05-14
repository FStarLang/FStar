open Prims
let subst_to_string :
  'Auu____4 . (FStar_Syntax_Syntax.bv * 'Auu____4) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____33 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____64  ->
              match uu____64 with
              | (b,uu____76) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____33 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____101 'Auu____102 .
    ('Auu____101 -> 'Auu____102 FStar_Pervasives_Native.option) ->
      'Auu____101 Prims.list ->
        ('Auu____101 Prims.list * 'Auu____102) FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____144 = f s0  in
          (match uu____144 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____177 'Auu____178 'Auu____179 .
    ('Auu____177 -> 'Auu____178 -> 'Auu____179) ->
      'Auu____179 ->
        ('Auu____177 * 'Auu____178) FStar_Pervasives_Native.option ->
          'Auu____179
  =
  fun f  ->
    fun x  ->
      fun uu___0_206  ->
        match uu___0_206 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____242 'Auu____243 'Auu____244 .
    ('Auu____242 -> 'Auu____243 FStar_Pervasives_Native.option) ->
      'Auu____242 Prims.list ->
        ('Auu____242 Prims.list -> 'Auu____243 -> 'Auu____244) ->
          'Auu____244 -> 'Auu____244
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____292 = apply_until_some f s  in
          FStar_All.pipe_right uu____292 (map_some_curry g t)
  
let compose_subst :
  'Auu____318 .
    ('Auu____318 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____318 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____318 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____369 ->
            FStar_Pervasives_Native.snd s2
        | uu____372 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____495 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____541;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____542;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____543;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____544;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____545;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____546;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____547;_},s)
        ->
        let uu____623 = FStar_Syntax_Unionfind.find uv  in
        (match uu____623 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____650 =
               let uu____661 =
                 let uu____673 = delay t' s  in force_uvar' uu____673  in
               FStar_Pervasives_Native.fst uu____661  in
             (uu____650, true)
         | uu____699 -> (t, false))
    | uu____714 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____752 = force_uvar' t  in
    match uu____752 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____812 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____812, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____930 = FStar_ST.op_Bang m  in
        (match uu____930 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____1012 = try_read_memo_aux t'  in
             (match uu____1012 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____1104 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____1137 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____1137
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____1173 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____1173 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____1177 -> u)
    | uu____1180 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_1220  ->
           match uu___1_1220 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____1242 =
                 let uu____1251 =
                   let uu____1262 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____1262  in
                 FStar_Syntax_Syntax.bv_to_name uu____1251  in
               FStar_Pervasives_Native.Some uu____1242
           | uu____1267 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_1315  ->
           match uu___2_1315 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____1338 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___108_1351 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___108_1351.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___108_1351.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____1338
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____1398 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_1427  ->
           match uu___3_1427 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____1435 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_1460  ->
           match uu___4_1460 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____1472 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____1502 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1514 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1514
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1518 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1518
  
let tag_with_range :
  'Auu____1528 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1528 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1566 =
            let uu____1568 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1569 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1568 uu____1569  in
          if uu____1566
          then t
          else
            (let r1 =
               let uu____1580 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1580
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1588 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1588
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1605 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1605
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___160_1639 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1640 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1640;
                       FStar_Syntax_Syntax.p =
                         (uu___160_1639.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___163_1664 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___163_1664.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___163_1664.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___168_1672 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___168_1672.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1690 .
    FStar_Ident.lident ->
      ('Auu____1690 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1722 =
            let uu____1724 =
              let uu____1725 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1725  in
            let uu____1726 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1724 uu____1726  in
          if uu____1722
          then l
          else
            (let uu____1734 =
               let uu____1735 = FStar_Ident.range_of_lid l  in
               let uu____1736 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1735 uu____1736  in
             FStar_Ident.set_lid_range l uu____1734)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1753 =
            let uu____1755 = FStar_Range.use_range r  in
            let uu____1756 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1755 uu____1756  in
          if uu____1753
          then r
          else
            (let uu____1760 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1760)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1923 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1943 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1948 -> tag_with_range t0 s
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
               let uu____2070 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____2071 =
                 let uu____2078 =
                   let uu____2079 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____2079  in
                 FStar_Syntax_Syntax.mk uu____2078  in
               uu____2071 FStar_Pervasives_Native.None uu____2070
           | uu____2084 ->
               let uu____2085 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____2085)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_2101  ->
              match uu___5_2101 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____2109 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____2109
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____2155 ->
          let uu___229_2164 = t  in
          let uu____2175 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____2180 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____2193 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____2204 =
            FStar_List.map
              (fun uu____2244  ->
                 match uu____2244 with
                 | (t1,imp) ->
                     let uu____2279 = subst' s t1  in
                     let uu____2288 = subst_imp' s imp  in
                     (uu____2279, uu____2288))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____2297 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____2175;
            FStar_Syntax_Syntax.effect_name = uu____2180;
            FStar_Syntax_Syntax.result_typ = uu____2193;
            FStar_Syntax_Syntax.effect_args = uu____2204;
            FStar_Syntax_Syntax.flags = uu____2297
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____2336 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____2369 = subst' s t1  in
               let uu____2378 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____2369 uu____2378
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____2403 = subst' s t1  in
               let uu____2412 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____2403 uu____2412
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____2425 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____2425)

and (subst_imp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____2457 =
            let uu____2458 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____2458  in
          FStar_Pervasives_Native.Some uu____2457
      | i1 -> i1

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
      | FStar_Syntax_Syntax.NT uu____2541 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____2577 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____2577) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____2577)
  =
  fun n1  ->
    fun s  ->
      let uu____2608 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____2608, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____2661  ->
      match uu____2661 with
      | (x,imp) ->
          let uu____2708 =
            let uu___288_2719 = x  in
            let uu____2730 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___288_2719.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___288_2719.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2730
            }  in
          let uu____2741 = subst_imp' s imp  in (uu____2708, uu____2741)
  
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
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
                  (let uu____2897 = shift_subst' i s  in
                   subst_binder' uu____2897 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____2936 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____2936) ->
        (FStar_Syntax_Syntax.term * 'Auu____2936)
  =
  fun s  ->
    fun uu____2962  ->
      match uu____2962 with
      | (t,imp) -> let uu____2981 = subst' s t  in (uu____2981, imp)
  
let subst_args' :
  'Auu____3000 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____3000) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____3000) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____3116 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____3150 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____3218  ->
                      fun uu____3219  ->
                        match (uu____3218, uu____3219) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____3327 = aux n2 p2  in
                            (match uu____3327 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____3150 with
             | (pats1,n2) ->
                 ((let uu___325_3401 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___325_3401.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___330_3451 = x  in
              let uu____3462 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___330_3451.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___330_3451.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____3462
              }  in
            ((let uu___333_3475 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___333_3475.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___338_3506 = x  in
              let uu____3517 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___338_3506.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___338_3506.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____3517
              }  in
            ((let uu___341_3530 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___341_3530.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___348_3579 = x  in
              let uu____3590 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___348_3579.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___348_3579.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____3590
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___352_3612 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___352_3612.FStar_Syntax_Syntax.p)
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
          let uu____3706 =
            let uu___359_3721 = rc  in
            let uu____3736 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___359_3721.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3736;
              FStar_Syntax_Syntax.residual_flags =
                (uu___359_3721.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____3706
  
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
               (fun uu____3841  ->
                  match uu____3841 with
                  | (x',uu____3855) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_3881 =
          match uu___7_3881 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_3912  ->
                        match uu___6_3912 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____3939 = should_retain x  in
                            if uu____3939
                            then
                              let uu____3944 =
                                let uu____3945 =
                                  let uu____3961 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____3961)  in
                                FStar_Syntax_Syntax.NT uu____3945  in
                              [uu____3944]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____4003 = should_retain x  in
                            if uu____4003
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___386_4019 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___386_4019.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___386_4019.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____4057 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____4071 -> []))
                 in
              let uu____4072 = aux rest  in FStar_List.append hd1 uu____4072
           in
        let uu____4075 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____4075 with
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
        let uu____4154 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____4154  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____4161 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____4210 ->
               let t1 =
                 let uu____4232 =
                   let uu____4249 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____4249  in
                 uu____4232 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____4331 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____4332 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____4337 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____4383 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____4383 with
           | FStar_Pervasives_Native.None  ->
               let uu____4400 =
                 let uu___419_4411 = t  in
                 let uu____4422 =
                   let uu____4423 =
                     let uu____4444 = compose_uvar_subst uv s0 s  in
                     (uv, uu____4444)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____4423  in
                 {
                   FStar_Syntax_Syntax.n = uu____4422;
                   FStar_Syntax_Syntax.pos =
                     (uu___419_4411.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___419_4411.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____4400 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____4484 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____4485 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____4491 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____4518 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____4518 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____4575 =
            let uu____4576 =
              let uu____4601 = subst' s t0  in
              let uu____4612 = subst_args' s args  in
              (uu____4601, uu____4612)  in
            FStar_Syntax_Syntax.Tm_app uu____4576  in
          mk1 uu____4575
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____4805 = subst' s t1  in FStar_Util.Inl uu____4805
            | FStar_Util.Inr c ->
                let uu____4847 = subst_comp' s c  in
                FStar_Util.Inr uu____4847
             in
          let uu____4870 =
            let uu____4871 =
              let uu____4918 = subst' s t0  in
              let uu____4929 =
                let uu____4958 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____4958)  in
              (uu____4918, uu____4929, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4871  in
          mk1 uu____4870
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____5121 =
            let uu____5122 =
              let uu____5157 = subst_binders' s bs  in
              let uu____5171 = subst' s' body  in
              let uu____5182 = push_subst_lcomp s' lopt  in
              (uu____5157, uu____5171, uu____5182)  in
            FStar_Syntax_Syntax.Tm_abs uu____5122  in
          mk1 uu____5121
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____5272 =
            let uu____5273 =
              let uu____5297 = subst_binders' s bs  in
              let uu____5311 =
                let uu____5322 = shift_subst' n1 s  in
                subst_comp' uu____5322 comp  in
              (uu____5297, uu____5311)  in
            FStar_Syntax_Syntax.Tm_arrow uu____5273  in
          mk1 uu____5272
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___466_5385 = x  in
            let uu____5396 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___466_5385.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___466_5385.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5396
            }  in
          let phi1 =
            let uu____5416 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____5416 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____5631  ->
                    match uu____5631 with
                    | (pat,wopt,branch) ->
                        let uu____5699 = subst_pat' s pat  in
                        (match uu____5699 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____5762 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____5762
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
                      let uu____5975 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____5975
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___504_6042 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_6042.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_6042.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___509_6073 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___509_6073.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___509_6073.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___509_6073.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___509_6073.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____6181 =
            let uu____6182 =
              let uu____6193 = subst' s t0  in
              let uu____6204 =
                let uu____6205 =
                  let uu____6234 = FStar_List.map (subst' s) bs  in
                  let uu____6255 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____6234, uu____6255)  in
                FStar_Syntax_Syntax.Meta_pattern uu____6205  in
              (uu____6193, uu____6204)  in
            FStar_Syntax_Syntax.Tm_meta uu____6182  in
          mk1 uu____6181
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____6393 =
            let uu____6394 =
              let uu____6405 = subst' s t0  in
              let uu____6416 =
                let uu____6417 =
                  let uu____6432 = subst' s t1  in (m, uu____6432)  in
                FStar_Syntax_Syntax.Meta_monadic uu____6417  in
              (uu____6405, uu____6416)  in
            FStar_Syntax_Syntax.Tm_meta uu____6394  in
          mk1 uu____6393
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____6503 =
            let uu____6504 =
              let uu____6515 = subst' s t0  in
              let uu____6526 =
                let uu____6527 =
                  let uu____6548 = subst' s t1  in (m1, m2, uu____6548)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____6527  in
              (uu____6515, uu____6526)  in
            FStar_Syntax_Syntax.Tm_meta uu____6504  in
          mk1 uu____6503
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____6603 =
                 let uu____6604 =
                   let uu____6617 = subst' s tm  in (uu____6617, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____6604  in
               mk1 uu____6603
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____6663 =
            let uu____6664 = let uu____6675 = subst' s t1  in (uu____6675, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____6664  in
          mk1 uu____6663
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____6721 = force_uvar t1  in
    match uu____6721 with
    | (t2,uu____6738) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____6823 =
                 let uu____6832 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____6832  in
               FStar_ST.op_Colon_Equals memo uu____6823);
              compress t2)
         | uu____6884 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____6943 =
        let uu____6944 =
          let uu____6945 =
            let uu____6946 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____6946  in
          FStar_Syntax_Syntax.SomeUseRange uu____6945  in
        ([], uu____6944)  in
      subst' uu____6943 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  =
  fun s  -> fun imp  -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____7019 =
      FStar_List.fold_right
        (fun uu____7051  ->
           fun uu____7052  ->
             match (uu____7051, uu____7052) with
             | ((x,uu____7097),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____7019 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___583_7355 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____7366 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___583_7355.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___583_7355.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____7366
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____7381 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____7381
             in
          let uu____7392 = aux bs' o1  in
          (match uu____7392 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____7488 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____7488
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____7548 = open_binders' bs  in
      match uu____7548 with
      | (bs',opening) ->
          let uu____7604 = subst opening t  in (bs', uu____7604, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____7644 = open_term' bs t  in
      match uu____7644 with | (b,t1,uu____7665) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____7705 = open_binders' bs  in
      match uu____7705 with
      | (bs',opening) ->
          let uu____7759 = subst_comp opening t  in (bs', uu____7759)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____7830 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____7870 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____7956  ->
                    fun uu____7957  ->
                      match (uu____7956, uu____7957) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____8098 = open_pat_aux sub2 p2  in
                          (match uu____8098 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____7870 with
           | (pats1,sub2) ->
               ((let uu___630_8247 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___630_8247.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___634_8295 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____8306 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___634_8295.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___634_8295.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____8306
            }  in
          let sub2 =
            let uu____8320 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____8320
             in
          ((let uu___638_8339 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___638_8339.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___642_8362 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____8373 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___642_8362.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___642_8362.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____8373
            }  in
          let sub2 =
            let uu____8387 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____8387
             in
          ((let uu___646_8406 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___646_8406.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___652_8447 = x  in
            let uu____8458 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___652_8447.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___652_8447.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____8458
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___656_8486 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___656_8486.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____8512  ->
    match uu____8512 with
    | (p,wopt,e) ->
        let uu____8558 = open_pat p  in
        (match uu____8558 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____8611 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____8611
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____8662 = open_branch' br  in
    match uu____8662 with | (br1,uu____8668) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____8692 = closing_subst bs  in subst uu____8692 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____8718 = closing_subst bs  in subst_comp uu____8718 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___688_8836 = x  in
            let uu____8847 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___688_8836.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___688_8836.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____8847
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____8862 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____8862
             in
          let uu____8873 = aux s' tl1  in (x1, imp1) :: uu____8873
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
        (fun uu____8939  ->
           let uu____8940 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____8940)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____9017 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____9057 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____9143  ->
                    fun uu____9144  ->
                      match (uu____9143, uu____9144) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____9285 = aux sub2 p2  in
                          (match uu____9285 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____9057 with
           | (pats1,sub2) ->
               ((let uu___719_9434 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___719_9434.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___723_9482 = x  in
            let uu____9493 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___723_9482.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___723_9482.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____9493
            }  in
          let sub2 =
            let uu____9507 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____9507
             in
          ((let uu___727_9526 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___727_9526.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___731_9549 = x  in
            let uu____9560 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___731_9549.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___731_9549.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____9560
            }  in
          let sub2 =
            let uu____9574 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____9574
             in
          ((let uu___735_9593 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___735_9593.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___741_9634 = x  in
            let uu____9645 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___741_9634.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___741_9634.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____9645
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___745_9673 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___745_9673.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____9695  ->
    match uu____9695 with
    | (p,wopt,e) ->
        let uu____9737 = close_pat p  in
        (match uu____9737 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____9807 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____9807
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
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
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____9964 = univ_var_opening us  in
      match uu____9964 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____10045 = univ_var_opening us  in
      match uu____10045 with
      | (s,us') -> let uu____10078 = subst_comp s c  in (us', uu____10078)
  
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
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____10228 =
        let uu____10247 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____10247
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____10315  ->
                 match uu____10315 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____10397 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____10397  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___797_10437 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___797_10437.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___797_10437.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___797_10437.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___797_10437.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___797_10437.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___797_10437.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____10228 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____10588 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____10624  ->
                             match uu____10624 with
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
                    match uu____10588 with
                    | (uu____10702,us,u_let_rec_opening) ->
                        let uu___814_10719 = lb  in
                        let uu____10734 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____10745 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___814_10719.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____10734;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___814_10719.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____10745;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___814_10719.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___814_10719.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____10832 =
        let uu____10840 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____10840
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____10876  ->
                 match uu____10876 with
                 | (i,out) ->
                     let uu____10906 =
                       let uu____10909 =
                         let uu____10910 =
                           let uu____10921 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____10921, i)  in
                         FStar_Syntax_Syntax.NM uu____10910  in
                       uu____10909 :: out  in
                     ((i + (Prims.parse_int "1")), uu____10906)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____10832 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11036 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____11058  ->
                             match uu____11058 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____11036 with
                    | (uu____11100,u_let_rec_closing) ->
                        let uu___836_11108 = lb  in
                        let uu____11123 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____11134 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___836_11108.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___836_11108.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____11123;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___836_11108.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____11134;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___836_11108.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___836_11108.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____11177  ->
      match uu____11177 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____11236  ->
                   match uu____11236 with
                   | (x,uu____11250) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____11300  ->
      match uu____11300 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____11346 = subst s t  in (us', uu____11346)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____11379  ->
      match uu____11379 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____11407 = subst s1 t  in (us, uu____11407)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____11477  ->
              match uu____11477 with
              | (x,uu____11491) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun b  ->
    fun t  ->
      let uu____11545 = open_term [b] t  in
      match uu____11545 with
      | (b1::[],t1) -> (b1, t1)
      | uu____11631 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____11697 =
        let uu____11706 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____11706 t  in
      match uu____11697 with
      | (bs,t1) ->
          let uu____11748 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____11748, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____11832 = open_term_bvs [bv] t  in
      match uu____11832 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____11912 -> failwith "impossible: open_term_bv"
  