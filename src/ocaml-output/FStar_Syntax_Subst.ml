open Prims
let subst_to_string :
  'Auu____42207 .
    (FStar_Syntax_Syntax.bv * 'Auu____42207) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____42226 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____42247  ->
              match uu____42247 with
              | (b,uu____42254) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____42226 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____42269 'Auu____42270 .
    ('Auu____42269 -> 'Auu____42270 FStar_Pervasives_Native.option) ->
      'Auu____42269 Prims.list ->
        ('Auu____42269 Prims.list * 'Auu____42270)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____42312 = f s0  in
          (match uu____42312 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____42345 'Auu____42346 'Auu____42347 .
    ('Auu____42345 -> 'Auu____42346 -> 'Auu____42347) ->
      'Auu____42347 ->
        ('Auu____42345 * 'Auu____42346) FStar_Pervasives_Native.option ->
          'Auu____42347
  =
  fun f  ->
    fun x  ->
      fun uu___391_42374  ->
        match uu___391_42374 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____42410 'Auu____42411 'Auu____42412 .
    ('Auu____42410 -> 'Auu____42411 FStar_Pervasives_Native.option) ->
      'Auu____42410 Prims.list ->
        ('Auu____42410 Prims.list -> 'Auu____42411 -> 'Auu____42412) ->
          'Auu____42412 -> 'Auu____42412
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____42460 = apply_until_some f s  in
          FStar_All.pipe_right uu____42460 (map_some_curry g t)
  
let compose_subst :
  'Auu____42486 .
    ('Auu____42486 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____42486 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____42486 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____42537 ->
            FStar_Pervasives_Native.snd s2
        | uu____42540 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____42623 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____42649;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____42650;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____42651;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____42652;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____42653;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____42654;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____42655;_},s)
        ->
        let uu____42704 = FStar_Syntax_Unionfind.find uv  in
        (match uu____42704 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____42715 =
               let uu____42718 =
                 let uu____42726 = delay t' s  in force_uvar' uu____42726  in
               FStar_Pervasives_Native.fst uu____42718  in
             (uu____42715, true)
         | uu____42736 -> (t, false))
    | uu____42743 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____42765 = force_uvar' t  in
    match uu____42765 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____42801 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____42801, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____42875 = FStar_ST.op_Bang m  in
        (match uu____42875 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____42947 = try_read_memo_aux t'  in
             (match uu____42947 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____43029 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43046 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____43046
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____43072 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____43072 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____43076 -> u)
    | uu____43079 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_43101  ->
           match uu___392_43101 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____43109 =
                 let uu____43110 =
                   let uu____43111 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____43111  in
                 FStar_Syntax_Syntax.bv_to_name uu____43110  in
               FStar_Pervasives_Native.Some uu____43109
           | uu____43112 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_43138  ->
           match uu___393_43138 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____43147 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_43152 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_43152.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_43152.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____43147
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____43163 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_43188  ->
           match uu___394_43188 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____43196 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_43217  ->
           match uu___395_43217 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____43225 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____43253 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____43263 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____43263
      | FStar_Syntax_Syntax.U_max us ->
          let uu____43267 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____43267
  
let tag_with_range :
  'Auu____43277 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____43277 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43303 =
            let uu____43305 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____43306 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43305 uu____43306  in
          if uu____43303
          then t
          else
            (let r1 =
               let uu____43313 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____43313
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____43316 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____43316
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____43318 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____43318
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_43324 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____43325 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____43325;
                       FStar_Syntax_Syntax.p =
                         (uu___551_43324.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_43327 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_43327.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_43327.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_43329 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_43329.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____43339 .
    FStar_Ident.lident ->
      ('Auu____43339 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43359 =
            let uu____43361 =
              let uu____43362 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____43362  in
            let uu____43363 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43361 uu____43363  in
          if uu____43359
          then l
          else
            (let uu____43367 =
               let uu____43368 = FStar_Ident.range_of_lid l  in
               let uu____43369 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____43368 uu____43369  in
             FStar_Ident.set_lid_range l uu____43367)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____43386 =
            let uu____43388 = FStar_Range.use_range r  in
            let uu____43389 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____43388 uu____43389  in
          if uu____43386
          then r
          else
            (let uu____43393 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____43393)
  
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
      | uu____43514 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____43522 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____43527 -> tag_with_range t0 s
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
               let uu____43596 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____43597 =
                 let uu____43604 =
                   let uu____43605 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____43605  in
                 FStar_Syntax_Syntax.mk uu____43604  in
               uu____43597 FStar_Pervasives_Native.None uu____43596
           | uu____43613 ->
               let uu____43614 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____43614)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_43626  ->
              match uu___396_43626 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____43630 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____43630
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
      | uu____43658 ->
          let uu___620_43667 = t  in
          let uu____43668 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____43673 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____43678 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____43681 =
            FStar_List.map
              (fun uu____43709  ->
                 match uu____43709 with
                 | (t1,imp) ->
                     let uu____43728 = subst' s t1  in
                     let uu____43729 = subst_imp' s imp  in
                     (uu____43728, uu____43729))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____43734 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____43668;
            FStar_Syntax_Syntax.effect_name = uu____43673;
            FStar_Syntax_Syntax.result_typ = uu____43678;
            FStar_Syntax_Syntax.effect_args = uu____43681;
            FStar_Syntax_Syntax.flags = uu____43734
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
      | uu____43765 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____43786 = subst' s t1  in
               let uu____43787 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____43786 uu____43787
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____43804 = subst' s t1  in
               let uu____43805 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____43804 uu____43805
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____43813 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____43813)

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
          let uu____43831 =
            let uu____43832 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____43832  in
          FStar_Pervasives_Native.Some uu____43831
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
      | FStar_Syntax_Syntax.NT uu____43871 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____43898 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43898) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43898)
  =
  fun n1  ->
    fun s  ->
      let uu____43929 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____43929, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____43972  ->
      match uu____43972 with
      | (x,imp) ->
          let uu____43999 =
            let uu___679_44000 = x  in
            let uu____44001 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_44000.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_44000.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____44001
            }  in
          let uu____44004 = subst_imp' s imp  in (uu____43999, uu____44004)
  
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
                  (let uu____44110 = shift_subst' i s  in
                   subst_binder' uu____44110 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____44149 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44149) ->
        (FStar_Syntax_Syntax.term * 'Auu____44149)
  =
  fun s  ->
    fun uu____44167  ->
      match uu____44167 with
      | (t,imp) -> let uu____44174 = subst' s t  in (uu____44174, imp)
  
let subst_args' :
  'Auu____44181 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44181) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____44181) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____44275 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____44297 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____44359  ->
                      fun uu____44360  ->
                        match (uu____44359, uu____44360) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____44456 = aux n2 p2  in
                            (match uu____44456 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____44297 with
             | (pats1,n2) ->
                 ((let uu___716_44530 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_44530.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_44556 = x  in
              let uu____44557 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_44556.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_44556.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44557
              }  in
            ((let uu___724_44562 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_44562.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_44575 = x  in
              let uu____44576 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_44575.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_44575.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44576
              }  in
            ((let uu___732_44581 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_44581.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_44599 = x  in
              let uu____44600 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_44599.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_44599.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44600
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_44606 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_44606.FStar_Syntax_Syntax.p)
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
          let uu____44632 =
            let uu___750_44633 = rc  in
            let uu____44634 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_44633.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____44634;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_44633.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____44632
  
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
               (fun uu____44684  ->
                  match uu____44684 with
                  | (x',uu____44693) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_44709 =
          match uu___398_44709 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_44740  ->
                        match uu___397_44740 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____44749 = should_retain x  in
                            if uu____44749
                            then
                              let uu____44754 =
                                let uu____44755 =
                                  let uu____44762 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____44762)  in
                                FStar_Syntax_Syntax.NT uu____44755  in
                              [uu____44754]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____44777 = should_retain x  in
                            if uu____44777
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_44785 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_44785.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_44785.FStar_Syntax_Syntax.sort)
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
                               | uu____44795 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____44800 -> []))
                 in
              let uu____44801 = aux rest  in
              FStar_List.append hd1 uu____44801
           in
        let uu____44804 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____44804 with
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
        let uu____44867 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____44867
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____44870 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____44899 ->
               let t1 =
                 let uu____44909 =
                   let uu____44918 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____44918  in
                 uu____44909 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____44968 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____44969 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____44974 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____45001 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____45001 with
           | FStar_Pervasives_Native.None  ->
               let uu____45006 =
                 let uu___810_45009 = t  in
                 let uu____45012 =
                   let uu____45013 =
                     let uu____45026 = compose_uvar_subst uv s0 s  in
                     (uv, uu____45026)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____45013  in
                 {
                   FStar_Syntax_Syntax.n = uu____45012;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_45009.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_45009.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____45006 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____45050 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____45051 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____45052 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____45066 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____45066 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____45099 =
            let uu____45100 =
              let uu____45117 = subst' s t0  in
              let uu____45120 = subst_args' s args  in
              (uu____45117, uu____45120)  in
            FStar_Syntax_Syntax.Tm_app uu____45100  in
          mk1 uu____45099
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____45221 = subst' s t1  in FStar_Util.Inl uu____45221
            | FStar_Util.Inr c ->
                let uu____45235 = subst_comp' s c  in
                FStar_Util.Inr uu____45235
             in
          let uu____45242 =
            let uu____45243 =
              let uu____45270 = subst' s t0  in
              let uu____45273 =
                let uu____45290 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____45290)  in
              (uu____45270, uu____45273, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____45243  in
          mk1 uu____45242
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____45376 =
            let uu____45377 =
              let uu____45396 = subst_binders' s bs  in
              let uu____45405 = subst' s' body  in
              let uu____45408 = push_subst_lcomp s' lopt  in
              (uu____45396, uu____45405, uu____45408)  in
            FStar_Syntax_Syntax.Tm_abs uu____45377  in
          mk1 uu____45376
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____45452 =
            let uu____45453 =
              let uu____45468 = subst_binders' s bs  in
              let uu____45477 =
                let uu____45480 = shift_subst' n1 s  in
                subst_comp' uu____45480 comp  in
              (uu____45468, uu____45477)  in
            FStar_Syntax_Syntax.Tm_arrow uu____45453  in
          mk1 uu____45452
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_45510 = x  in
            let uu____45511 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_45510.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_45510.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____45511
            }  in
          let phi1 =
            let uu____45515 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____45515 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____45631  ->
                    match uu____45631 with
                    | (pat,wopt,branch) ->
                        let uu____45661 = subst_pat' s pat  in
                        (match uu____45661 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____45692 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____45692
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
                      let uu____45764 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____45764
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_45782 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_45782.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_45782.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_45784 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_45784.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_45784.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_45784.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_45784.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____45815 =
            let uu____45816 =
              let uu____45823 = subst' s t0  in
              let uu____45826 =
                let uu____45827 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____45827  in
              (uu____45823, uu____45826)  in
            FStar_Syntax_Syntax.Tm_meta uu____45816  in
          mk1 uu____45815
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____45893 =
            let uu____45894 =
              let uu____45901 = subst' s t0  in
              let uu____45904 =
                let uu____45905 =
                  let uu____45912 = subst' s t1  in (m, uu____45912)  in
                FStar_Syntax_Syntax.Meta_monadic uu____45905  in
              (uu____45901, uu____45904)  in
            FStar_Syntax_Syntax.Tm_meta uu____45894  in
          mk1 uu____45893
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____45931 =
            let uu____45932 =
              let uu____45939 = subst' s t0  in
              let uu____45942 =
                let uu____45943 =
                  let uu____45952 = subst' s t1  in (m1, m2, uu____45952)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____45943  in
              (uu____45939, uu____45942)  in
            FStar_Syntax_Syntax.Tm_meta uu____45932  in
          mk1 uu____45931
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____45967 =
                 let uu____45968 =
                   let uu____45975 = subst' s tm  in (uu____45975, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____45968  in
               mk1 uu____45967
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____45989 =
            let uu____45990 =
              let uu____45997 = subst' s t1  in (uu____45997, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____45990  in
          mk1 uu____45989
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____46011 = force_uvar t1  in
    match uu____46011 with
    | (t2,uu____46020) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____46073 =
                 let uu____46078 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____46078  in
               FStar_ST.op_Colon_Equals memo uu____46073);
              compress t2)
         | uu____46132 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____46167 =
        let uu____46168 =
          let uu____46169 =
            let uu____46170 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____46170  in
          FStar_Syntax_Syntax.SomeUseRange uu____46169  in
        ([], uu____46168)  in
      subst' uu____46167 t
  
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
    let uu____46231 =
      FStar_List.fold_right
        (fun uu____46258  ->
           fun uu____46259  ->
             match (uu____46258, uu____46259) with
             | ((x,uu____46294),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____46231 FStar_Pervasives_Native.fst
  
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
            let uu___972_46452 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____46453 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_46452.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_46452.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____46453
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____46460 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____46460
             in
          let uu____46466 = aux bs' o1  in
          (match uu____46466 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____46527 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____46527
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____46565 = open_binders' bs  in
      match uu____46565 with
      | (bs',opening) ->
          let uu____46602 = subst opening t  in (bs', uu____46602, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____46618 = open_term' bs t  in
      match uu____46618 with | (b,t1,uu____46631) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____46647 = open_binders' bs  in
      match uu____46647 with
      | (bs',opening) ->
          let uu____46682 = subst_comp opening t  in (bs', uu____46682)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____46732 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____46757 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____46828  ->
                    fun uu____46829  ->
                      match (uu____46828, uu____46829) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____46943 = open_pat_aux sub2 p2  in
                          (match uu____46943 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____46757 with
           | (pats1,sub2) ->
               ((let uu___1019_47053 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_47053.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_47074 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47075 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_47074.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_47074.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47075
            }  in
          let sub2 =
            let uu____47081 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47081
             in
          ((let uu___1027_47092 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_47092.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_47097 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47098 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_47097.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_47097.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47098
            }  in
          let sub2 =
            let uu____47104 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47104
             in
          ((let uu___1035_47115 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_47115.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_47125 = x  in
            let uu____47126 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_47125.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_47125.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47126
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_47135 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_47135.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____47149  ->
    match uu____47149 with
    | (p,wopt,e) ->
        let uu____47173 = open_pat p  in
        (match uu____47173 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47202 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____47202
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____47222 = open_branch' br  in
    match uu____47222 with | (br1,uu____47228) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____47240 = closing_subst bs  in subst uu____47240 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____47254 = closing_subst bs  in subst_comp uu____47254 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_47322 = x  in
            let uu____47323 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_47322.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_47322.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47323
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____47330 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47330
             in
          let uu____47336 = aux s' tl1  in (x1, imp1) :: uu____47336
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
        (fun uu____47363  ->
           let uu____47364 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____47364)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____47418 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____47443 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____47514  ->
                    fun uu____47515  ->
                      match (uu____47514, uu____47515) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47629 = aux sub2 p2  in
                          (match uu____47629 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____47443 with
           | (pats1,sub2) ->
               ((let uu___1108_47739 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_47739.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_47760 = x  in
            let uu____47761 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_47760.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_47760.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47761
            }  in
          let sub2 =
            let uu____47767 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47767
             in
          ((let uu___1116_47778 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_47778.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_47783 = x  in
            let uu____47784 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_47783.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_47783.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47784
            }  in
          let sub2 =
            let uu____47790 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47790
             in
          ((let uu___1124_47801 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_47801.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_47811 = x  in
            let uu____47812 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_47811.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_47811.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47812
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_47821 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_47821.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____47831  ->
    match uu____47831 with
    | (p,wopt,e) ->
        let uu____47851 = close_pat p  in
        (match uu____47851 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47888 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____47888
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
      let uu____47976 = univ_var_opening us  in
      match uu____47976 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____48019 = univ_var_opening us  in
      match uu____48019 with
      | (s,us') -> let uu____48042 = subst_comp s c  in (us', uu____48042)
  
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
      let uu____48105 =
        let uu____48117 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48117
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48157  ->
                 match uu____48157 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____48194 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____48194  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_48202 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_48202.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____48105 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____48245 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48275  ->
                             match uu____48275 with
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
                    match uu____48245 with
                    | (uu____48324,us,u_let_rec_opening) ->
                        let uu___1203_48337 = lb  in
                        let uu____48338 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48341 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_48337.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____48338;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_48337.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48341;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_48337.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_48337.FStar_Syntax_Syntax.lbpos)
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
      let uu____48368 =
        let uu____48376 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48376
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48405  ->
                 match uu____48405 with
                 | (i,out) ->
                     let uu____48428 =
                       let uu____48431 =
                         let uu____48432 =
                           let uu____48438 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____48438, i)  in
                         FStar_Syntax_Syntax.NM uu____48432  in
                       uu____48431 :: out  in
                     ((i + (Prims.parse_int "1")), uu____48428)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____48368 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____48477 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48497  ->
                             match uu____48497 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____48477 with
                    | (uu____48528,u_let_rec_closing) ->
                        let uu___1225_48536 = lb  in
                        let uu____48537 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48540 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_48536.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_48536.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____48537;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_48536.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48540;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_48536.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_48536.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____48556  ->
      match uu____48556 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____48591  ->
                   match uu____48591 with
                   | (x,uu____48600) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____48627  ->
      match uu____48627 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____48657 = subst s t  in (us', uu____48657)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____48676  ->
      match uu____48676 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____48690 = subst s1 t  in (us, uu____48690)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____48731  ->
              match uu____48731 with
              | (x,uu____48740) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____48767 = open_term [b] t  in
      match uu____48767 with
      | (b1::[],t1) -> (b1, t1)
      | uu____48808 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____48839 =
        let uu____48844 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____48844 t  in
      match uu____48839 with
      | (bs,t1) ->
          let uu____48859 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____48859, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____48887 = open_term_bvs [bv] t  in
      match uu____48887 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____48902 -> failwith "impossible: open_term_bv"
  