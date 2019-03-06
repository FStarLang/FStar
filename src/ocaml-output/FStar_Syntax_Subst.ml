open Prims
let subst_to_string :
  'Auu____42277 .
    (FStar_Syntax_Syntax.bv * 'Auu____42277) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____42296 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____42317  ->
              match uu____42317 with
              | (b,uu____42324) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____42296 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____42339 'Auu____42340 .
    ('Auu____42339 -> 'Auu____42340 FStar_Pervasives_Native.option) ->
      'Auu____42339 Prims.list ->
        ('Auu____42339 Prims.list * 'Auu____42340)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____42382 = f s0  in
          (match uu____42382 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____42415 'Auu____42416 'Auu____42417 .
    ('Auu____42415 -> 'Auu____42416 -> 'Auu____42417) ->
      'Auu____42417 ->
        ('Auu____42415 * 'Auu____42416) FStar_Pervasives_Native.option ->
          'Auu____42417
  =
  fun f  ->
    fun x  ->
      fun uu___391_42444  ->
        match uu___391_42444 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____42480 'Auu____42481 'Auu____42482 .
    ('Auu____42480 -> 'Auu____42481 FStar_Pervasives_Native.option) ->
      'Auu____42480 Prims.list ->
        ('Auu____42480 Prims.list -> 'Auu____42481 -> 'Auu____42482) ->
          'Auu____42482 -> 'Auu____42482
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____42530 = apply_until_some f s  in
          FStar_All.pipe_right uu____42530 (map_some_curry g t)
  
let compose_subst :
  'Auu____42556 .
    ('Auu____42556 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____42556 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____42556 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____42607 ->
            FStar_Pervasives_Native.snd s2
        | uu____42610 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____42693 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____42719;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____42720;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____42721;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____42722;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____42723;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____42724;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____42725;_},s)
        ->
        let uu____42774 = FStar_Syntax_Unionfind.find uv  in
        (match uu____42774 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____42785 =
               let uu____42788 =
                 let uu____42796 = delay t' s  in force_uvar' uu____42796  in
               FStar_Pervasives_Native.fst uu____42788  in
             (uu____42785, true)
         | uu____42806 -> (t, false))
    | uu____42813 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____42835 = force_uvar' t  in
    match uu____42835 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____42871 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____42871, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____42945 = FStar_ST.op_Bang m  in
        (match uu____42945 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____43017 = try_read_memo_aux t'  in
             (match uu____43017 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____43099 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43116 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____43116
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____43142 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____43142 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____43146 -> u)
    | uu____43149 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_43171  ->
           match uu___392_43171 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____43179 =
                 let uu____43180 =
                   let uu____43181 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____43181  in
                 FStar_Syntax_Syntax.bv_to_name uu____43180  in
               FStar_Pervasives_Native.Some uu____43179
           | uu____43182 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_43208  ->
           match uu___393_43208 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____43217 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_43222 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_43222.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_43222.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____43217
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____43233 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_43258  ->
           match uu___394_43258 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____43266 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_43287  ->
           match uu___395_43287 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____43295 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____43323 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____43333 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____43333
      | FStar_Syntax_Syntax.U_max us ->
          let uu____43337 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____43337
  
let tag_with_range :
  'Auu____43347 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____43347 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43373 =
            let uu____43375 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____43376 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43375 uu____43376  in
          if uu____43373
          then t
          else
            (let r1 =
               let uu____43383 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____43383
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____43386 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____43386
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____43388 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____43388
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_43394 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____43395 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____43395;
                       FStar_Syntax_Syntax.p =
                         (uu___551_43394.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_43397 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_43397.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_43397.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_43399 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_43399.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____43409 .
    FStar_Ident.lident ->
      ('Auu____43409 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43429 =
            let uu____43431 =
              let uu____43432 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____43432  in
            let uu____43433 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43431 uu____43433  in
          if uu____43429
          then l
          else
            (let uu____43437 =
               let uu____43438 = FStar_Ident.range_of_lid l  in
               let uu____43439 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____43438 uu____43439  in
             FStar_Ident.set_lid_range l uu____43437)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____43456 =
            let uu____43458 = FStar_Range.use_range r  in
            let uu____43459 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____43458 uu____43459  in
          if uu____43456
          then r
          else
            (let uu____43463 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____43463)
  
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
      | uu____43584 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____43592 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____43597 -> tag_with_range t0 s
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
               let uu____43666 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____43667 =
                 let uu____43674 =
                   let uu____43675 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____43675  in
                 FStar_Syntax_Syntax.mk uu____43674  in
               uu____43667 FStar_Pervasives_Native.None uu____43666
           | uu____43683 ->
               let uu____43684 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____43684)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_43696  ->
              match uu___396_43696 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____43700 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____43700
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
      | uu____43728 ->
          let uu___620_43737 = t  in
          let uu____43738 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____43743 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____43748 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____43751 =
            FStar_List.map
              (fun uu____43779  ->
                 match uu____43779 with
                 | (t1,imp) ->
                     let uu____43798 = subst' s t1  in
                     let uu____43799 = subst_imp' s imp  in
                     (uu____43798, uu____43799))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____43804 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____43738;
            FStar_Syntax_Syntax.effect_name = uu____43743;
            FStar_Syntax_Syntax.result_typ = uu____43748;
            FStar_Syntax_Syntax.effect_args = uu____43751;
            FStar_Syntax_Syntax.flags = uu____43804
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
      | uu____43835 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____43856 = subst' s t1  in
               let uu____43857 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____43856 uu____43857
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____43874 = subst' s t1  in
               let uu____43875 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____43874 uu____43875
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____43883 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____43883)

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
          let uu____43901 =
            let uu____43902 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____43902  in
          FStar_Pervasives_Native.Some uu____43901
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
      | FStar_Syntax_Syntax.NT uu____43941 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____43968 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43968) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43968)
  =
  fun n1  ->
    fun s  ->
      let uu____43999 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____43999, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____44042  ->
      match uu____44042 with
      | (x,imp) ->
          let uu____44069 =
            let uu___679_44070 = x  in
            let uu____44071 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_44070.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_44070.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____44071
            }  in
          let uu____44074 = subst_imp' s imp  in (uu____44069, uu____44074)
  
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
                  (let uu____44180 = shift_subst' i s  in
                   subst_binder' uu____44180 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____44219 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44219) ->
        (FStar_Syntax_Syntax.term * 'Auu____44219)
  =
  fun s  ->
    fun uu____44237  ->
      match uu____44237 with
      | (t,imp) -> let uu____44244 = subst' s t  in (uu____44244, imp)
  
let subst_args' :
  'Auu____44251 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44251) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____44251) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____44345 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____44367 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____44429  ->
                      fun uu____44430  ->
                        match (uu____44429, uu____44430) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____44526 = aux n2 p2  in
                            (match uu____44526 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____44367 with
             | (pats1,n2) ->
                 ((let uu___716_44600 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_44600.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_44626 = x  in
              let uu____44627 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_44626.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_44626.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44627
              }  in
            ((let uu___724_44632 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_44632.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_44645 = x  in
              let uu____44646 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_44645.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_44645.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44646
              }  in
            ((let uu___732_44651 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_44651.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_44669 = x  in
              let uu____44670 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_44669.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_44669.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44670
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_44676 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_44676.FStar_Syntax_Syntax.p)
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
          let uu____44702 =
            let uu___750_44703 = rc  in
            let uu____44704 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_44703.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____44704;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_44703.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____44702
  
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
               (fun uu____44754  ->
                  match uu____44754 with
                  | (x',uu____44763) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_44779 =
          match uu___398_44779 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_44810  ->
                        match uu___397_44810 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____44819 = should_retain x  in
                            if uu____44819
                            then
                              let uu____44824 =
                                let uu____44825 =
                                  let uu____44832 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____44832)  in
                                FStar_Syntax_Syntax.NT uu____44825  in
                              [uu____44824]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____44847 = should_retain x  in
                            if uu____44847
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_44855 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_44855.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_44855.FStar_Syntax_Syntax.sort)
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
                               | uu____44865 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____44870 -> []))
                 in
              let uu____44871 = aux rest  in
              FStar_List.append hd1 uu____44871
           in
        let uu____44874 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____44874 with
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
        let uu____44937 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____44937
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____44940 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____44969 ->
               let t1 =
                 let uu____44979 =
                   let uu____44988 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____44988  in
                 uu____44979 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____45038 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____45039 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____45044 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____45071 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____45071 with
           | FStar_Pervasives_Native.None  ->
               let uu____45076 =
                 let uu___810_45079 = t  in
                 let uu____45082 =
                   let uu____45083 =
                     let uu____45096 = compose_uvar_subst uv s0 s  in
                     (uv, uu____45096)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____45083  in
                 {
                   FStar_Syntax_Syntax.n = uu____45082;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_45079.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_45079.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____45076 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____45120 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____45121 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____45122 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____45136 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____45136 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____45169 =
            let uu____45170 =
              let uu____45187 = subst' s t0  in
              let uu____45190 = subst_args' s args  in
              (uu____45187, uu____45190)  in
            FStar_Syntax_Syntax.Tm_app uu____45170  in
          mk1 uu____45169
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____45291 = subst' s t1  in FStar_Util.Inl uu____45291
            | FStar_Util.Inr c ->
                let uu____45305 = subst_comp' s c  in
                FStar_Util.Inr uu____45305
             in
          let uu____45312 =
            let uu____45313 =
              let uu____45340 = subst' s t0  in
              let uu____45343 =
                let uu____45360 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____45360)  in
              (uu____45340, uu____45343, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____45313  in
          mk1 uu____45312
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____45446 =
            let uu____45447 =
              let uu____45466 = subst_binders' s bs  in
              let uu____45475 = subst' s' body  in
              let uu____45478 = push_subst_lcomp s' lopt  in
              (uu____45466, uu____45475, uu____45478)  in
            FStar_Syntax_Syntax.Tm_abs uu____45447  in
          mk1 uu____45446
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____45522 =
            let uu____45523 =
              let uu____45538 = subst_binders' s bs  in
              let uu____45547 =
                let uu____45550 = shift_subst' n1 s  in
                subst_comp' uu____45550 comp  in
              (uu____45538, uu____45547)  in
            FStar_Syntax_Syntax.Tm_arrow uu____45523  in
          mk1 uu____45522
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_45580 = x  in
            let uu____45581 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_45580.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_45580.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____45581
            }  in
          let phi1 =
            let uu____45585 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____45585 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____45701  ->
                    match uu____45701 with
                    | (pat,wopt,branch) ->
                        let uu____45731 = subst_pat' s pat  in
                        (match uu____45731 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____45762 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____45762
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
                      let uu____45834 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____45834
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_45852 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_45852.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_45852.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_45854 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_45854.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_45854.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_45854.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_45854.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____45885 =
            let uu____45886 =
              let uu____45893 = subst' s t0  in
              let uu____45896 =
                let uu____45897 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____45897  in
              (uu____45893, uu____45896)  in
            FStar_Syntax_Syntax.Tm_meta uu____45886  in
          mk1 uu____45885
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____45963 =
            let uu____45964 =
              let uu____45971 = subst' s t0  in
              let uu____45974 =
                let uu____45975 =
                  let uu____45982 = subst' s t1  in (m, uu____45982)  in
                FStar_Syntax_Syntax.Meta_monadic uu____45975  in
              (uu____45971, uu____45974)  in
            FStar_Syntax_Syntax.Tm_meta uu____45964  in
          mk1 uu____45963
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____46001 =
            let uu____46002 =
              let uu____46009 = subst' s t0  in
              let uu____46012 =
                let uu____46013 =
                  let uu____46022 = subst' s t1  in (m1, m2, uu____46022)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____46013  in
              (uu____46009, uu____46012)  in
            FStar_Syntax_Syntax.Tm_meta uu____46002  in
          mk1 uu____46001
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____46037 =
                 let uu____46038 =
                   let uu____46045 = subst' s tm  in (uu____46045, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____46038  in
               mk1 uu____46037
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____46059 =
            let uu____46060 =
              let uu____46067 = subst' s t1  in (uu____46067, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____46060  in
          mk1 uu____46059
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____46081 = force_uvar t1  in
    match uu____46081 with
    | (t2,uu____46090) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____46143 =
                 let uu____46148 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____46148  in
               FStar_ST.op_Colon_Equals memo uu____46143);
              compress t2)
         | uu____46202 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____46237 =
        let uu____46238 =
          let uu____46239 =
            let uu____46240 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____46240  in
          FStar_Syntax_Syntax.SomeUseRange uu____46239  in
        ([], uu____46238)  in
      subst' uu____46237 t
  
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
    let uu____46301 =
      FStar_List.fold_right
        (fun uu____46328  ->
           fun uu____46329  ->
             match (uu____46328, uu____46329) with
             | ((x,uu____46364),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____46301 FStar_Pervasives_Native.fst
  
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
            let uu___972_46522 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____46523 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_46522.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_46522.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____46523
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____46530 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____46530
             in
          let uu____46536 = aux bs' o1  in
          (match uu____46536 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____46597 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____46597
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____46635 = open_binders' bs  in
      match uu____46635 with
      | (bs',opening) ->
          let uu____46672 = subst opening t  in (bs', uu____46672, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____46688 = open_term' bs t  in
      match uu____46688 with | (b,t1,uu____46701) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____46717 = open_binders' bs  in
      match uu____46717 with
      | (bs',opening) ->
          let uu____46752 = subst_comp opening t  in (bs', uu____46752)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____46802 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____46827 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____46898  ->
                    fun uu____46899  ->
                      match (uu____46898, uu____46899) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47013 = open_pat_aux sub2 p2  in
                          (match uu____47013 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____46827 with
           | (pats1,sub2) ->
               ((let uu___1019_47123 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_47123.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_47144 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47145 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_47144.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_47144.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47145
            }  in
          let sub2 =
            let uu____47151 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47151
             in
          ((let uu___1027_47162 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_47162.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_47167 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47168 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_47167.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_47167.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47168
            }  in
          let sub2 =
            let uu____47174 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47174
             in
          ((let uu___1035_47185 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_47185.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_47195 = x  in
            let uu____47196 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_47195.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_47195.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47196
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_47205 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_47205.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____47219  ->
    match uu____47219 with
    | (p,wopt,e) ->
        let uu____47243 = open_pat p  in
        (match uu____47243 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47272 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____47272
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____47292 = open_branch' br  in
    match uu____47292 with | (br1,uu____47298) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____47310 = closing_subst bs  in subst uu____47310 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____47324 = closing_subst bs  in subst_comp uu____47324 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_47392 = x  in
            let uu____47393 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_47392.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_47392.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47393
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____47400 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47400
             in
          let uu____47406 = aux s' tl1  in (x1, imp1) :: uu____47406
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
        (fun uu____47433  ->
           let uu____47434 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____47434)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____47488 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____47513 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____47584  ->
                    fun uu____47585  ->
                      match (uu____47584, uu____47585) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47699 = aux sub2 p2  in
                          (match uu____47699 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____47513 with
           | (pats1,sub2) ->
               ((let uu___1108_47809 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_47809.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_47830 = x  in
            let uu____47831 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_47830.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_47830.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47831
            }  in
          let sub2 =
            let uu____47837 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47837
             in
          ((let uu___1116_47848 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_47848.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_47853 = x  in
            let uu____47854 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_47853.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_47853.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47854
            }  in
          let sub2 =
            let uu____47860 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47860
             in
          ((let uu___1124_47871 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_47871.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_47881 = x  in
            let uu____47882 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_47881.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_47881.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47882
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_47891 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_47891.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____47901  ->
    match uu____47901 with
    | (p,wopt,e) ->
        let uu____47921 = close_pat p  in
        (match uu____47921 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47958 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____47958
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
      let uu____48046 = univ_var_opening us  in
      match uu____48046 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____48089 = univ_var_opening us  in
      match uu____48089 with
      | (s,us') -> let uu____48112 = subst_comp s c  in (us', uu____48112)
  
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
      let uu____48175 =
        let uu____48187 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48187
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48227  ->
                 match uu____48227 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____48264 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____48264  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_48272 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_48272.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____48175 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____48315 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48345  ->
                             match uu____48345 with
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
                    match uu____48315 with
                    | (uu____48394,us,u_let_rec_opening) ->
                        let uu___1203_48407 = lb  in
                        let uu____48408 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48411 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_48407.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____48408;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_48407.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48411;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_48407.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_48407.FStar_Syntax_Syntax.lbpos)
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
      let uu____48438 =
        let uu____48446 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48446
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48475  ->
                 match uu____48475 with
                 | (i,out) ->
                     let uu____48498 =
                       let uu____48501 =
                         let uu____48502 =
                           let uu____48508 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____48508, i)  in
                         FStar_Syntax_Syntax.NM uu____48502  in
                       uu____48501 :: out  in
                     ((i + (Prims.parse_int "1")), uu____48498)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____48438 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____48547 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48567  ->
                             match uu____48567 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____48547 with
                    | (uu____48598,u_let_rec_closing) ->
                        let uu___1225_48606 = lb  in
                        let uu____48607 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48610 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_48606.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_48606.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____48607;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_48606.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48610;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_48606.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_48606.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____48626  ->
      match uu____48626 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____48661  ->
                   match uu____48661 with
                   | (x,uu____48670) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____48697  ->
      match uu____48697 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____48727 = subst s t  in (us', uu____48727)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____48746  ->
      match uu____48746 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____48760 = subst s1 t  in (us, uu____48760)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____48801  ->
              match uu____48801 with
              | (x,uu____48810) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____48837 = open_term [b] t  in
      match uu____48837 with
      | (b1::[],t1) -> (b1, t1)
      | uu____48878 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____48909 =
        let uu____48914 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____48914 t  in
      match uu____48909 with
      | (bs,t1) ->
          let uu____48929 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____48929, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____48957 = open_term_bvs [bv] t  in
      match uu____48957 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____48972 -> failwith "impossible: open_term_bv"
  