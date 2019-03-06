open Prims
let subst_to_string :
  'Auu____38407 .
    (FStar_Syntax_Syntax.bv * 'Auu____38407) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____38426 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____38447  ->
              match uu____38447 with
              | (b,uu____38454) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____38426 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____38469 'Auu____38470 .
    ('Auu____38469 -> 'Auu____38470 FStar_Pervasives_Native.option) ->
      'Auu____38469 Prims.list ->
        ('Auu____38469 Prims.list * 'Auu____38470)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____38512 = f s0  in
          (match uu____38512 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____38545 'Auu____38546 'Auu____38547 .
    ('Auu____38545 -> 'Auu____38546 -> 'Auu____38547) ->
      'Auu____38547 ->
        ('Auu____38545 * 'Auu____38546) FStar_Pervasives_Native.option ->
          'Auu____38547
  =
  fun f  ->
    fun x  ->
      fun uu___391_38574  ->
        match uu___391_38574 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____38610 'Auu____38611 'Auu____38612 .
    ('Auu____38610 -> 'Auu____38611 FStar_Pervasives_Native.option) ->
      'Auu____38610 Prims.list ->
        ('Auu____38610 Prims.list -> 'Auu____38611 -> 'Auu____38612) ->
          'Auu____38612 -> 'Auu____38612
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____38660 = apply_until_some f s  in
          FStar_All.pipe_right uu____38660 (map_some_curry g t)
  
let compose_subst :
  'Auu____38686 .
    ('Auu____38686 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____38686 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____38686 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____38737 ->
            FStar_Pervasives_Native.snd s2
        | uu____38740 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____38823 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____38849;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____38850;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____38851;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____38852;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____38853;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____38854;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____38855;_},s)
        ->
        let uu____38904 = FStar_Syntax_Unionfind.find uv  in
        (match uu____38904 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____38915 =
               let uu____38918 =
                 let uu____38926 = delay t' s  in force_uvar' uu____38926  in
               FStar_Pervasives_Native.fst uu____38918  in
             (uu____38915, true)
         | uu____38936 -> (t, false))
    | uu____38943 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____38965 = force_uvar' t  in
    match uu____38965 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____39001 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____39001, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____39075 = FStar_ST.op_Bang m  in
        (match uu____39075 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____39125 = try_read_memo_aux t'  in
             (match uu____39125 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____39185 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____39202 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____39202
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____39228 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____39228 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____39232 -> u)
    | uu____39235 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_39257  ->
           match uu___392_39257 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____39265 =
                 let uu____39266 =
                   let uu____39267 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____39267  in
                 FStar_Syntax_Syntax.bv_to_name uu____39266  in
               FStar_Pervasives_Native.Some uu____39265
           | uu____39268 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_39294  ->
           match uu___393_39294 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____39303 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_39308 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_39308.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_39308.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____39303
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____39319 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_39344  ->
           match uu___394_39344 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____39352 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_39373  ->
           match uu___395_39373 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____39381 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____39409 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____39419 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____39419
      | FStar_Syntax_Syntax.U_max us ->
          let uu____39423 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____39423
  
let tag_with_range :
  'Auu____39433 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____39433 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____39459 =
            let uu____39461 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____39462 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____39461 uu____39462  in
          if uu____39459
          then t
          else
            (let r1 =
               let uu____39469 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____39469
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____39472 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____39472
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____39474 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____39474
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_39480 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____39481 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____39481;
                       FStar_Syntax_Syntax.p =
                         (uu___551_39480.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_39483 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_39483.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_39483.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_39485 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_39485.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____39495 .
    FStar_Ident.lident ->
      ('Auu____39495 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____39515 =
            let uu____39517 =
              let uu____39518 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____39518  in
            let uu____39519 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____39517 uu____39519  in
          if uu____39515
          then l
          else
            (let uu____39523 =
               let uu____39524 = FStar_Ident.range_of_lid l  in
               let uu____39525 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____39524 uu____39525  in
             FStar_Ident.set_lid_range l uu____39523)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____39542 =
            let uu____39544 = FStar_Range.use_range r  in
            let uu____39545 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____39544 uu____39545  in
          if uu____39542
          then r
          else
            (let uu____39549 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____39549)
  
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
      | uu____39670 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____39678 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____39683 -> tag_with_range t0 s
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
               let uu____39752 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____39753 =
                 let uu____39760 =
                   let uu____39761 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____39761  in
                 FStar_Syntax_Syntax.mk uu____39760  in
               uu____39753 FStar_Pervasives_Native.None uu____39752
           | uu____39766 ->
               let uu____39767 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____39767)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_39779  ->
              match uu___396_39779 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____39783 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____39783
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
      | uu____39811 ->
          let uu___620_39820 = t  in
          let uu____39821 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____39826 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____39831 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____39834 =
            FStar_List.map
              (fun uu____39862  ->
                 match uu____39862 with
                 | (t1,imp) ->
                     let uu____39881 = subst' s t1  in
                     let uu____39882 = subst_imp' s imp  in
                     (uu____39881, uu____39882))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____39887 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____39821;
            FStar_Syntax_Syntax.effect_name = uu____39826;
            FStar_Syntax_Syntax.result_typ = uu____39831;
            FStar_Syntax_Syntax.effect_args = uu____39834;
            FStar_Syntax_Syntax.flags = uu____39887
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
      | uu____39918 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____39939 = subst' s t1  in
               let uu____39940 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____39939 uu____39940
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____39957 = subst' s t1  in
               let uu____39958 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____39957 uu____39958
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____39966 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____39966)

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
          let uu____39984 =
            let uu____39985 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____39985  in
          FStar_Pervasives_Native.Some uu____39984
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
      | FStar_Syntax_Syntax.NT uu____40024 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____40051 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____40051) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____40051)
  =
  fun n1  ->
    fun s  ->
      let uu____40082 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____40082, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____40125  ->
      match uu____40125 with
      | (x,imp) ->
          let uu____40152 =
            let uu___679_40153 = x  in
            let uu____40154 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_40153.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_40153.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____40154
            }  in
          let uu____40157 = subst_imp' s imp  in (uu____40152, uu____40157)
  
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
                  (let uu____40263 = shift_subst' i s  in
                   subst_binder' uu____40263 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____40302 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____40302) ->
        (FStar_Syntax_Syntax.term * 'Auu____40302)
  =
  fun s  ->
    fun uu____40320  ->
      match uu____40320 with
      | (t,imp) -> let uu____40327 = subst' s t  in (uu____40327, imp)
  
let subst_args' :
  'Auu____40334 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____40334) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____40334) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____40428 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____40450 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____40512  ->
                      fun uu____40513  ->
                        match (uu____40512, uu____40513) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____40609 = aux n2 p2  in
                            (match uu____40609 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____40450 with
             | (pats1,n2) ->
                 ((let uu___716_40683 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_40683.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_40709 = x  in
              let uu____40710 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_40709.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_40709.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40710
              }  in
            ((let uu___724_40715 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_40715.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_40728 = x  in
              let uu____40729 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_40728.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_40728.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40729
              }  in
            ((let uu___732_40734 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_40734.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_40752 = x  in
              let uu____40753 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_40752.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_40752.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40753
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_40759 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_40759.FStar_Syntax_Syntax.p)
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
          let uu____40785 =
            let uu___750_40786 = rc  in
            let uu____40787 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_40786.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____40787;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_40786.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____40785
  
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
               (fun uu____40837  ->
                  match uu____40837 with
                  | (x',uu____40846) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_40862 =
          match uu___398_40862 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_40893  ->
                        match uu___397_40893 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____40902 = should_retain x  in
                            if uu____40902
                            then
                              let uu____40907 =
                                let uu____40908 =
                                  let uu____40915 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____40915)  in
                                FStar_Syntax_Syntax.NT uu____40908  in
                              [uu____40907]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____40930 = should_retain x  in
                            if uu____40930
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_40938 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_40938.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_40938.FStar_Syntax_Syntax.sort)
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
                               | uu____40948 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____40953 -> []))
                 in
              let uu____40954 = aux rest  in
              FStar_List.append hd1 uu____40954
           in
        let uu____40957 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____40957 with
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
        let uu____41020 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____41020
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____41023 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____41052 ->
               let t1 =
                 let uu____41062 =
                   let uu____41071 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____41071  in
                 uu____41062 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____41121 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____41122 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____41127 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____41154 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____41154 with
           | FStar_Pervasives_Native.None  ->
               let uu____41159 =
                 let uu___810_41162 = t  in
                 let uu____41165 =
                   let uu____41166 =
                     let uu____41179 = compose_uvar_subst uv s0 s  in
                     (uv, uu____41179)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____41166  in
                 {
                   FStar_Syntax_Syntax.n = uu____41165;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_41162.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_41162.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____41159 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____41203 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____41204 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____41205 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____41219 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____41219 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____41252 =
            let uu____41253 =
              let uu____41270 = subst' s t0  in
              let uu____41273 = subst_args' s args  in
              (uu____41270, uu____41273)  in
            FStar_Syntax_Syntax.Tm_app uu____41253  in
          mk1 uu____41252
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____41374 = subst' s t1  in FStar_Util.Inl uu____41374
            | FStar_Util.Inr c ->
                let uu____41388 = subst_comp' s c  in
                FStar_Util.Inr uu____41388
             in
          let uu____41395 =
            let uu____41396 =
              let uu____41423 = subst' s t0  in
              let uu____41426 =
                let uu____41443 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____41443)  in
              (uu____41423, uu____41426, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____41396  in
          mk1 uu____41395
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____41525 =
            let uu____41526 =
              let uu____41545 = subst_binders' s bs  in
              let uu____41554 = subst' s' body  in
              let uu____41557 = push_subst_lcomp s' lopt  in
              (uu____41545, uu____41554, uu____41557)  in
            FStar_Syntax_Syntax.Tm_abs uu____41526  in
          mk1 uu____41525
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____41601 =
            let uu____41602 =
              let uu____41617 = subst_binders' s bs  in
              let uu____41626 =
                let uu____41629 = shift_subst' n1 s  in
                subst_comp' uu____41629 comp  in
              (uu____41617, uu____41626)  in
            FStar_Syntax_Syntax.Tm_arrow uu____41602  in
          mk1 uu____41601
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_41655 = x  in
            let uu____41656 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_41655.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_41655.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____41656
            }  in
          let phi1 =
            let uu____41660 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____41660 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____41776  ->
                    match uu____41776 with
                    | (pat,wopt,branch) ->
                        let uu____41806 = subst_pat' s pat  in
                        (match uu____41806 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____41837 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____41837
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
                      let uu____41905 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____41905
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_41923 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_41923.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_41923.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_41925 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_41925.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_41925.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_41925.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_41925.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____41956 =
            let uu____41957 =
              let uu____41964 = subst' s t0  in
              let uu____41967 =
                let uu____41968 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____41968  in
              (uu____41964, uu____41967)  in
            FStar_Syntax_Syntax.Tm_meta uu____41957  in
          mk1 uu____41956
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____42034 =
            let uu____42035 =
              let uu____42042 = subst' s t0  in
              let uu____42045 =
                let uu____42046 =
                  let uu____42053 = subst' s t1  in (m, uu____42053)  in
                FStar_Syntax_Syntax.Meta_monadic uu____42046  in
              (uu____42042, uu____42045)  in
            FStar_Syntax_Syntax.Tm_meta uu____42035  in
          mk1 uu____42034
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____42072 =
            let uu____42073 =
              let uu____42080 = subst' s t0  in
              let uu____42083 =
                let uu____42084 =
                  let uu____42093 = subst' s t1  in (m1, m2, uu____42093)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____42084  in
              (uu____42080, uu____42083)  in
            FStar_Syntax_Syntax.Tm_meta uu____42073  in
          mk1 uu____42072
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____42108 =
                 let uu____42109 =
                   let uu____42116 = subst' s tm  in (uu____42116, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____42109  in
               mk1 uu____42108
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____42130 =
            let uu____42131 =
              let uu____42138 = subst' s t1  in (uu____42138, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____42131  in
          mk1 uu____42130
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____42152 = force_uvar t1  in
    match uu____42152 with
    | (t2,uu____42161) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____42214 =
                 let uu____42219 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____42219  in
               FStar_ST.op_Colon_Equals memo uu____42214);
              compress t2)
         | uu____42251 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____42286 =
        let uu____42287 =
          let uu____42288 =
            let uu____42289 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____42289  in
          FStar_Syntax_Syntax.SomeUseRange uu____42288  in
        ([], uu____42287)  in
      subst' uu____42286 t
  
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
    let uu____42350 =
      FStar_List.fold_right
        (fun uu____42377  ->
           fun uu____42378  ->
             match (uu____42377, uu____42378) with
             | ((x,uu____42413),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____42350 FStar_Pervasives_Native.fst
  
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
            let uu___972_42571 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____42572 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_42571.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_42571.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42572
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____42579 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____42579
             in
          let uu____42585 = aux bs' o1  in
          (match uu____42585 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____42646 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____42646
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____42684 = open_binders' bs  in
      match uu____42684 with
      | (bs',opening) ->
          let uu____42721 = subst opening t  in (bs', uu____42721, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____42737 = open_term' bs t  in
      match uu____42737 with | (b,t1,uu____42750) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____42766 = open_binders' bs  in
      match uu____42766 with
      | (bs',opening) ->
          let uu____42801 = subst_comp opening t  in (bs', uu____42801)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____42851 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____42876 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____42947  ->
                    fun uu____42948  ->
                      match (uu____42947, uu____42948) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____43062 = open_pat_aux sub2 p2  in
                          (match uu____43062 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____42876 with
           | (pats1,sub2) ->
               ((let uu___1019_43172 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_43172.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_43193 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____43194 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_43193.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_43193.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43194
            }  in
          let sub2 =
            let uu____43200 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____43200
             in
          ((let uu___1027_43211 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_43211.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_43216 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____43217 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_43216.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_43216.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43217
            }  in
          let sub2 =
            let uu____43223 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____43223
             in
          ((let uu___1035_43234 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_43234.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_43244 = x  in
            let uu____43245 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_43244.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_43244.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43245
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_43254 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_43254.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____43268  ->
    match uu____43268 with
    | (p,wopt,e) ->
        let uu____43292 = open_pat p  in
        (match uu____43292 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____43321 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____43321
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____43341 = open_branch' br  in
    match uu____43341 with | (br1,uu____43347) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____43359 = closing_subst bs  in subst uu____43359 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____43373 = closing_subst bs  in subst_comp uu____43373 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_43441 = x  in
            let uu____43442 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_43441.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_43441.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43442
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____43449 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43449
             in
          let uu____43455 = aux s' tl1  in (x1, imp1) :: uu____43455
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
        (fun uu____43482  ->
           let uu____43483 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____43483)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____43537 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____43562 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____43633  ->
                    fun uu____43634  ->
                      match (uu____43633, uu____43634) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____43748 = aux sub2 p2  in
                          (match uu____43748 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____43562 with
           | (pats1,sub2) ->
               ((let uu___1108_43858 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_43858.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_43879 = x  in
            let uu____43880 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_43879.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_43879.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43880
            }  in
          let sub2 =
            let uu____43886 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43886
             in
          ((let uu___1116_43897 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_43897.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_43902 = x  in
            let uu____43903 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_43902.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_43902.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43903
            }  in
          let sub2 =
            let uu____43909 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43909
             in
          ((let uu___1124_43920 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_43920.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_43930 = x  in
            let uu____43931 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_43930.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_43930.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43931
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_43940 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_43940.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____43950  ->
    match uu____43950 with
    | (p,wopt,e) ->
        let uu____43970 = close_pat p  in
        (match uu____43970 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____44007 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____44007
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
      let uu____44095 = univ_var_opening us  in
      match uu____44095 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____44138 = univ_var_opening us  in
      match uu____44138 with
      | (s,us') -> let uu____44161 = subst_comp s c  in (us', uu____44161)
  
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
      let uu____44224 =
        let uu____44236 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____44236
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____44276  ->
                 match uu____44276 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____44313 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____44313  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_44321 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_44321.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____44224 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____44364 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____44394  ->
                             match uu____44394 with
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
                    match uu____44364 with
                    | (uu____44443,us,u_let_rec_opening) ->
                        let uu___1203_44456 = lb  in
                        let uu____44457 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____44460 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_44456.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____44457;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_44456.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____44460;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_44456.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_44456.FStar_Syntax_Syntax.lbpos)
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
      let uu____44487 =
        let uu____44495 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____44495
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____44524  ->
                 match uu____44524 with
                 | (i,out) ->
                     let uu____44547 =
                       let uu____44550 =
                         let uu____44551 =
                           let uu____44557 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____44557, i)  in
                         FStar_Syntax_Syntax.NM uu____44551  in
                       uu____44550 :: out  in
                     ((i + (Prims.parse_int "1")), uu____44547)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____44487 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____44596 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____44616  ->
                             match uu____44616 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____44596 with
                    | (uu____44647,u_let_rec_closing) ->
                        let uu___1225_44655 = lb  in
                        let uu____44656 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____44659 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_44655.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_44655.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____44656;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_44655.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____44659;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_44655.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_44655.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____44675  ->
      match uu____44675 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____44710  ->
                   match uu____44710 with
                   | (x,uu____44719) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____44740  ->
      match uu____44740 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____44764 = subst s t  in (us', uu____44764)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____44783  ->
      match uu____44783 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____44797 = subst s1 t  in (us, uu____44797)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____44838  ->
              match uu____44838 with
              | (x,uu____44847) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____44874 = open_term [b] t  in
      match uu____44874 with
      | (b1::[],t1) -> (b1, t1)
      | uu____44915 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____44946 =
        let uu____44951 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____44951 t  in
      match uu____44946 with
      | (bs,t1) ->
          let uu____44966 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____44966, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____44994 = open_term_bvs [bv] t  in
      match uu____44994 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____45009 -> failwith "impossible: open_term_bv"
  