open Prims
let subst_to_string :
  'Auu____42202 .
    (FStar_Syntax_Syntax.bv * 'Auu____42202) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____42221 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____42242  ->
              match uu____42242 with
              | (b,uu____42249) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____42221 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____42264 'Auu____42265 .
    ('Auu____42264 -> 'Auu____42265 FStar_Pervasives_Native.option) ->
      'Auu____42264 Prims.list ->
        ('Auu____42264 Prims.list * 'Auu____42265)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____42307 = f s0  in
          (match uu____42307 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____42340 'Auu____42341 'Auu____42342 .
    ('Auu____42340 -> 'Auu____42341 -> 'Auu____42342) ->
      'Auu____42342 ->
        ('Auu____42340 * 'Auu____42341) FStar_Pervasives_Native.option ->
          'Auu____42342
  =
  fun f  ->
    fun x  ->
      fun uu___391_42369  ->
        match uu___391_42369 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____42405 'Auu____42406 'Auu____42407 .
    ('Auu____42405 -> 'Auu____42406 FStar_Pervasives_Native.option) ->
      'Auu____42405 Prims.list ->
        ('Auu____42405 Prims.list -> 'Auu____42406 -> 'Auu____42407) ->
          'Auu____42407 -> 'Auu____42407
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____42455 = apply_until_some f s  in
          FStar_All.pipe_right uu____42455 (map_some_curry g t)
  
let compose_subst :
  'Auu____42481 .
    ('Auu____42481 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____42481 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____42481 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____42532 ->
            FStar_Pervasives_Native.snd s2
        | uu____42535 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____42618 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____42644;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____42645;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____42646;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____42647;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____42648;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____42649;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____42650;_},s)
        ->
        let uu____42699 = FStar_Syntax_Unionfind.find uv  in
        (match uu____42699 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____42710 =
               let uu____42713 =
                 let uu____42721 = delay t' s  in force_uvar' uu____42721  in
               FStar_Pervasives_Native.fst uu____42713  in
             (uu____42710, true)
         | uu____42731 -> (t, false))
    | uu____42738 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____42760 = force_uvar' t  in
    match uu____42760 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____42796 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____42796, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____42870 = FStar_ST.op_Bang m  in
        (match uu____42870 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____42942 = try_read_memo_aux t'  in
             (match uu____42942 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____43024 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43041 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____43041
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____43067 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____43067 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____43071 -> u)
    | uu____43074 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_43096  ->
           match uu___392_43096 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____43104 =
                 let uu____43105 =
                   let uu____43106 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____43106  in
                 FStar_Syntax_Syntax.bv_to_name uu____43105  in
               FStar_Pervasives_Native.Some uu____43104
           | uu____43107 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_43133  ->
           match uu___393_43133 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____43142 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_43147 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_43147.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_43147.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____43142
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____43158 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_43183  ->
           match uu___394_43183 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____43191 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_43212  ->
           match uu___395_43212 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____43220 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____43248 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____43258 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____43258
      | FStar_Syntax_Syntax.U_max us ->
          let uu____43262 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____43262
  
let tag_with_range :
  'Auu____43272 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____43272 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43298 =
            let uu____43300 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____43301 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43300 uu____43301  in
          if uu____43298
          then t
          else
            (let r1 =
               let uu____43308 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____43308
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____43311 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____43311
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____43313 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____43313
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_43319 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____43320 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____43320;
                       FStar_Syntax_Syntax.p =
                         (uu___551_43319.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_43322 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_43322.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_43322.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_43324 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_43324.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____43334 .
    FStar_Ident.lident ->
      ('Auu____43334 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43354 =
            let uu____43356 =
              let uu____43357 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____43357  in
            let uu____43358 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43356 uu____43358  in
          if uu____43354
          then l
          else
            (let uu____43362 =
               let uu____43363 = FStar_Ident.range_of_lid l  in
               let uu____43364 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____43363 uu____43364  in
             FStar_Ident.set_lid_range l uu____43362)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____43381 =
            let uu____43383 = FStar_Range.use_range r  in
            let uu____43384 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____43383 uu____43384  in
          if uu____43381
          then r
          else
            (let uu____43388 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____43388)
  
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
      | uu____43509 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____43517 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____43522 -> tag_with_range t0 s
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
               let uu____43591 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____43592 =
                 let uu____43599 =
                   let uu____43600 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____43600  in
                 FStar_Syntax_Syntax.mk uu____43599  in
               uu____43592 FStar_Pervasives_Native.None uu____43591
           | uu____43608 ->
               let uu____43609 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____43609)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_43621  ->
              match uu___396_43621 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____43625 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____43625
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
      | uu____43653 ->
          let uu___620_43662 = t  in
          let uu____43663 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____43668 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____43673 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____43676 =
            FStar_List.map
              (fun uu____43704  ->
                 match uu____43704 with
                 | (t1,imp) ->
                     let uu____43723 = subst' s t1  in
                     let uu____43724 = subst_imp' s imp  in
                     (uu____43723, uu____43724))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____43729 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____43663;
            FStar_Syntax_Syntax.effect_name = uu____43668;
            FStar_Syntax_Syntax.result_typ = uu____43673;
            FStar_Syntax_Syntax.effect_args = uu____43676;
            FStar_Syntax_Syntax.flags = uu____43729
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
      | uu____43760 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____43781 = subst' s t1  in
               let uu____43782 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____43781 uu____43782
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____43799 = subst' s t1  in
               let uu____43800 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____43799 uu____43800
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____43808 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____43808)

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
          let uu____43826 =
            let uu____43827 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____43827  in
          FStar_Pervasives_Native.Some uu____43826
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
      | FStar_Syntax_Syntax.NT uu____43866 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____43893 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43893) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43893)
  =
  fun n1  ->
    fun s  ->
      let uu____43924 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____43924, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____43967  ->
      match uu____43967 with
      | (x,imp) ->
          let uu____43994 =
            let uu___679_43995 = x  in
            let uu____43996 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_43995.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_43995.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43996
            }  in
          let uu____43999 = subst_imp' s imp  in (uu____43994, uu____43999)
  
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
                  (let uu____44105 = shift_subst' i s  in
                   subst_binder' uu____44105 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____44144 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44144) ->
        (FStar_Syntax_Syntax.term * 'Auu____44144)
  =
  fun s  ->
    fun uu____44162  ->
      match uu____44162 with
      | (t,imp) -> let uu____44169 = subst' s t  in (uu____44169, imp)
  
let subst_args' :
  'Auu____44176 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44176) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____44176) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____44270 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____44292 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____44354  ->
                      fun uu____44355  ->
                        match (uu____44354, uu____44355) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____44451 = aux n2 p2  in
                            (match uu____44451 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____44292 with
             | (pats1,n2) ->
                 ((let uu___716_44525 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_44525.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_44551 = x  in
              let uu____44552 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_44551.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_44551.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44552
              }  in
            ((let uu___724_44557 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_44557.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_44570 = x  in
              let uu____44571 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_44570.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_44570.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44571
              }  in
            ((let uu___732_44576 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_44576.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_44594 = x  in
              let uu____44595 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_44594.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_44594.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44595
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_44601 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_44601.FStar_Syntax_Syntax.p)
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
          let uu____44627 =
            let uu___750_44628 = rc  in
            let uu____44629 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_44628.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____44629;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_44628.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____44627
  
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
               (fun uu____44679  ->
                  match uu____44679 with
                  | (x',uu____44688) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_44704 =
          match uu___398_44704 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_44735  ->
                        match uu___397_44735 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____44744 = should_retain x  in
                            if uu____44744
                            then
                              let uu____44749 =
                                let uu____44750 =
                                  let uu____44757 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____44757)  in
                                FStar_Syntax_Syntax.NT uu____44750  in
                              [uu____44749]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____44772 = should_retain x  in
                            if uu____44772
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_44780 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_44780.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_44780.FStar_Syntax_Syntax.sort)
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
                               | uu____44790 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____44795 -> []))
                 in
              let uu____44796 = aux rest  in
              FStar_List.append hd1 uu____44796
           in
        let uu____44799 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____44799 with
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
        let uu____44862 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____44862
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____44865 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____44894 ->
               let t1 =
                 let uu____44904 =
                   let uu____44913 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____44913  in
                 uu____44904 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____44963 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____44964 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____44969 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____44996 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____44996 with
           | FStar_Pervasives_Native.None  ->
               let uu____45001 =
                 let uu___810_45004 = t  in
                 let uu____45007 =
                   let uu____45008 =
                     let uu____45021 = compose_uvar_subst uv s0 s  in
                     (uv, uu____45021)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____45008  in
                 {
                   FStar_Syntax_Syntax.n = uu____45007;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_45004.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_45004.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____45001 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____45045 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____45046 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____45047 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____45061 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____45061 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____45094 =
            let uu____45095 =
              let uu____45112 = subst' s t0  in
              let uu____45115 = subst_args' s args  in
              (uu____45112, uu____45115)  in
            FStar_Syntax_Syntax.Tm_app uu____45095  in
          mk1 uu____45094
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____45216 = subst' s t1  in FStar_Util.Inl uu____45216
            | FStar_Util.Inr c ->
                let uu____45230 = subst_comp' s c  in
                FStar_Util.Inr uu____45230
             in
          let uu____45237 =
            let uu____45238 =
              let uu____45265 = subst' s t0  in
              let uu____45268 =
                let uu____45285 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____45285)  in
              (uu____45265, uu____45268, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____45238  in
          mk1 uu____45237
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____45371 =
            let uu____45372 =
              let uu____45391 = subst_binders' s bs  in
              let uu____45400 = subst' s' body  in
              let uu____45403 = push_subst_lcomp s' lopt  in
              (uu____45391, uu____45400, uu____45403)  in
            FStar_Syntax_Syntax.Tm_abs uu____45372  in
          mk1 uu____45371
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____45447 =
            let uu____45448 =
              let uu____45463 = subst_binders' s bs  in
              let uu____45472 =
                let uu____45475 = shift_subst' n1 s  in
                subst_comp' uu____45475 comp  in
              (uu____45463, uu____45472)  in
            FStar_Syntax_Syntax.Tm_arrow uu____45448  in
          mk1 uu____45447
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_45505 = x  in
            let uu____45506 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_45505.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_45505.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____45506
            }  in
          let phi1 =
            let uu____45510 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____45510 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____45626  ->
                    match uu____45626 with
                    | (pat,wopt,branch) ->
                        let uu____45656 = subst_pat' s pat  in
                        (match uu____45656 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____45687 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____45687
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
                      let uu____45759 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____45759
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_45777 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_45777.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_45777.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_45779 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_45779.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_45779.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_45779.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_45779.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____45810 =
            let uu____45811 =
              let uu____45818 = subst' s t0  in
              let uu____45821 =
                let uu____45822 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____45822  in
              (uu____45818, uu____45821)  in
            FStar_Syntax_Syntax.Tm_meta uu____45811  in
          mk1 uu____45810
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____45888 =
            let uu____45889 =
              let uu____45896 = subst' s t0  in
              let uu____45899 =
                let uu____45900 =
                  let uu____45907 = subst' s t1  in (m, uu____45907)  in
                FStar_Syntax_Syntax.Meta_monadic uu____45900  in
              (uu____45896, uu____45899)  in
            FStar_Syntax_Syntax.Tm_meta uu____45889  in
          mk1 uu____45888
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____45926 =
            let uu____45927 =
              let uu____45934 = subst' s t0  in
              let uu____45937 =
                let uu____45938 =
                  let uu____45947 = subst' s t1  in (m1, m2, uu____45947)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____45938  in
              (uu____45934, uu____45937)  in
            FStar_Syntax_Syntax.Tm_meta uu____45927  in
          mk1 uu____45926
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____45962 =
                 let uu____45963 =
                   let uu____45970 = subst' s tm  in (uu____45970, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____45963  in
               mk1 uu____45962
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____45984 =
            let uu____45985 =
              let uu____45992 = subst' s t1  in (uu____45992, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____45985  in
          mk1 uu____45984
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____46006 = force_uvar t1  in
    match uu____46006 with
    | (t2,uu____46015) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____46068 =
                 let uu____46073 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____46073  in
               FStar_ST.op_Colon_Equals memo uu____46068);
              compress t2)
         | uu____46127 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____46162 =
        let uu____46163 =
          let uu____46164 =
            let uu____46165 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____46165  in
          FStar_Syntax_Syntax.SomeUseRange uu____46164  in
        ([], uu____46163)  in
      subst' uu____46162 t
  
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
    let uu____46226 =
      FStar_List.fold_right
        (fun uu____46253  ->
           fun uu____46254  ->
             match (uu____46253, uu____46254) with
             | ((x,uu____46289),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____46226 FStar_Pervasives_Native.fst
  
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
            let uu___972_46447 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____46448 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_46447.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_46447.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____46448
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____46455 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____46455
             in
          let uu____46461 = aux bs' o1  in
          (match uu____46461 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____46522 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____46522
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____46560 = open_binders' bs  in
      match uu____46560 with
      | (bs',opening) ->
          let uu____46597 = subst opening t  in (bs', uu____46597, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____46613 = open_term' bs t  in
      match uu____46613 with | (b,t1,uu____46626) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____46642 = open_binders' bs  in
      match uu____46642 with
      | (bs',opening) ->
          let uu____46677 = subst_comp opening t  in (bs', uu____46677)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____46727 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____46752 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____46823  ->
                    fun uu____46824  ->
                      match (uu____46823, uu____46824) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____46938 = open_pat_aux sub2 p2  in
                          (match uu____46938 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____46752 with
           | (pats1,sub2) ->
               ((let uu___1019_47048 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_47048.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_47069 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47070 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_47069.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_47069.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47070
            }  in
          let sub2 =
            let uu____47076 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47076
             in
          ((let uu___1027_47087 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_47087.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_47092 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47093 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_47092.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_47092.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47093
            }  in
          let sub2 =
            let uu____47099 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47099
             in
          ((let uu___1035_47110 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_47110.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_47120 = x  in
            let uu____47121 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_47120.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_47120.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47121
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_47130 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_47130.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____47144  ->
    match uu____47144 with
    | (p,wopt,e) ->
        let uu____47168 = open_pat p  in
        (match uu____47168 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47197 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____47197
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____47217 = open_branch' br  in
    match uu____47217 with | (br1,uu____47223) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____47235 = closing_subst bs  in subst uu____47235 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____47249 = closing_subst bs  in subst_comp uu____47249 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_47317 = x  in
            let uu____47318 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_47317.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_47317.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47318
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____47325 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47325
             in
          let uu____47331 = aux s' tl1  in (x1, imp1) :: uu____47331
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
        (fun uu____47358  ->
           let uu____47359 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____47359)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____47413 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____47438 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____47509  ->
                    fun uu____47510  ->
                      match (uu____47509, uu____47510) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47624 = aux sub2 p2  in
                          (match uu____47624 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____47438 with
           | (pats1,sub2) ->
               ((let uu___1108_47734 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_47734.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_47755 = x  in
            let uu____47756 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_47755.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_47755.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47756
            }  in
          let sub2 =
            let uu____47762 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47762
             in
          ((let uu___1116_47773 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_47773.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_47778 = x  in
            let uu____47779 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_47778.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_47778.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47779
            }  in
          let sub2 =
            let uu____47785 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47785
             in
          ((let uu___1124_47796 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_47796.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_47806 = x  in
            let uu____47807 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_47806.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_47806.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47807
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_47816 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_47816.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____47826  ->
    match uu____47826 with
    | (p,wopt,e) ->
        let uu____47846 = close_pat p  in
        (match uu____47846 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47883 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____47883
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
      let uu____47971 = univ_var_opening us  in
      match uu____47971 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____48014 = univ_var_opening us  in
      match uu____48014 with
      | (s,us') -> let uu____48037 = subst_comp s c  in (us', uu____48037)
  
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
      let uu____48100 =
        let uu____48112 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48112
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48152  ->
                 match uu____48152 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____48189 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____48189  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_48197 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_48197.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____48100 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____48240 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48270  ->
                             match uu____48270 with
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
                    match uu____48240 with
                    | (uu____48319,us,u_let_rec_opening) ->
                        let uu___1203_48332 = lb  in
                        let uu____48333 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48336 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_48332.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____48333;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_48332.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48336;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_48332.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_48332.FStar_Syntax_Syntax.lbpos)
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
      let uu____48363 =
        let uu____48371 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48371
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48400  ->
                 match uu____48400 with
                 | (i,out) ->
                     let uu____48423 =
                       let uu____48426 =
                         let uu____48427 =
                           let uu____48433 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____48433, i)  in
                         FStar_Syntax_Syntax.NM uu____48427  in
                       uu____48426 :: out  in
                     ((i + (Prims.parse_int "1")), uu____48423)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____48363 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____48472 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48492  ->
                             match uu____48492 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____48472 with
                    | (uu____48523,u_let_rec_closing) ->
                        let uu___1225_48531 = lb  in
                        let uu____48532 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48535 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_48531.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_48531.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____48532;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_48531.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48535;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_48531.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_48531.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____48551  ->
      match uu____48551 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____48586  ->
                   match uu____48586 with
                   | (x,uu____48595) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____48622  ->
      match uu____48622 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____48652 = subst s t  in (us', uu____48652)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____48671  ->
      match uu____48671 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____48685 = subst s1 t  in (us, uu____48685)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____48726  ->
              match uu____48726 with
              | (x,uu____48735) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____48762 = open_term [b] t  in
      match uu____48762 with
      | (b1::[],t1) -> (b1, t1)
      | uu____48803 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____48834 =
        let uu____48839 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____48839 t  in
      match uu____48834 with
      | (bs,t1) ->
          let uu____48854 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____48854, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____48882 = open_term_bvs [bv] t  in
      match uu____48882 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____48897 -> failwith "impossible: open_term_bv"
  