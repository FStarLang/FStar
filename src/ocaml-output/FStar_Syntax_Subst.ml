open Prims
let subst_to_string :
  'Auu____42276 .
    (FStar_Syntax_Syntax.bv * 'Auu____42276) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____42295 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____42316  ->
              match uu____42316 with
              | (b,uu____42323) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____42295 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____42338 'Auu____42339 .
    ('Auu____42338 -> 'Auu____42339 FStar_Pervasives_Native.option) ->
      'Auu____42338 Prims.list ->
        ('Auu____42338 Prims.list * 'Auu____42339)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____42381 = f s0  in
          (match uu____42381 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____42414 'Auu____42415 'Auu____42416 .
    ('Auu____42414 -> 'Auu____42415 -> 'Auu____42416) ->
      'Auu____42416 ->
        ('Auu____42414 * 'Auu____42415) FStar_Pervasives_Native.option ->
          'Auu____42416
  =
  fun f  ->
    fun x  ->
      fun uu___391_42443  ->
        match uu___391_42443 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____42479 'Auu____42480 'Auu____42481 .
    ('Auu____42479 -> 'Auu____42480 FStar_Pervasives_Native.option) ->
      'Auu____42479 Prims.list ->
        ('Auu____42479 Prims.list -> 'Auu____42480 -> 'Auu____42481) ->
          'Auu____42481 -> 'Auu____42481
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____42529 = apply_until_some f s  in
          FStar_All.pipe_right uu____42529 (map_some_curry g t)
  
let compose_subst :
  'Auu____42555 .
    ('Auu____42555 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____42555 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____42555 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____42606 ->
            FStar_Pervasives_Native.snd s2
        | uu____42609 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____42692 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____42718;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____42719;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____42720;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____42721;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____42722;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____42723;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____42724;_},s)
        ->
        let uu____42773 = FStar_Syntax_Unionfind.find uv  in
        (match uu____42773 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____42784 =
               let uu____42787 =
                 let uu____42795 = delay t' s  in force_uvar' uu____42795  in
               FStar_Pervasives_Native.fst uu____42787  in
             (uu____42784, true)
         | uu____42805 -> (t, false))
    | uu____42812 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____42834 = force_uvar' t  in
    match uu____42834 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____42870 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____42870, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____42944 = FStar_ST.op_Bang m  in
        (match uu____42944 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____43016 = try_read_memo_aux t'  in
             (match uu____43016 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____43098 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43115 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____43115
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____43141 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____43141 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____43145 -> u)
    | uu____43148 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_43170  ->
           match uu___392_43170 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____43178 =
                 let uu____43179 =
                   let uu____43180 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____43180  in
                 FStar_Syntax_Syntax.bv_to_name uu____43179  in
               FStar_Pervasives_Native.Some uu____43178
           | uu____43181 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_43207  ->
           match uu___393_43207 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____43216 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_43221 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_43221.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_43221.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____43216
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____43232 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_43257  ->
           match uu___394_43257 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____43265 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_43286  ->
           match uu___395_43286 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____43294 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____43322 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____43332 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____43332
      | FStar_Syntax_Syntax.U_max us ->
          let uu____43336 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____43336
  
let tag_with_range :
  'Auu____43346 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____43346 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43372 =
            let uu____43374 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____43375 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43374 uu____43375  in
          if uu____43372
          then t
          else
            (let r1 =
               let uu____43382 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____43382
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____43385 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____43385
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____43387 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____43387
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_43393 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____43394 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____43394;
                       FStar_Syntax_Syntax.p =
                         (uu___551_43393.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_43396 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_43396.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_43396.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_43398 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_43398.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____43408 .
    FStar_Ident.lident ->
      ('Auu____43408 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43428 =
            let uu____43430 =
              let uu____43431 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____43431  in
            let uu____43432 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43430 uu____43432  in
          if uu____43428
          then l
          else
            (let uu____43436 =
               let uu____43437 = FStar_Ident.range_of_lid l  in
               let uu____43438 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____43437 uu____43438  in
             FStar_Ident.set_lid_range l uu____43436)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____43455 =
            let uu____43457 = FStar_Range.use_range r  in
            let uu____43458 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____43457 uu____43458  in
          if uu____43455
          then r
          else
            (let uu____43462 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____43462)
  
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
      | uu____43583 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____43591 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____43596 -> tag_with_range t0 s
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
               let uu____43665 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____43666 =
                 let uu____43673 =
                   let uu____43674 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____43674  in
                 FStar_Syntax_Syntax.mk uu____43673  in
               uu____43666 FStar_Pervasives_Native.None uu____43665
           | uu____43682 ->
               let uu____43683 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____43683)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_43695  ->
              match uu___396_43695 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____43699 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____43699
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
      | uu____43727 ->
          let uu___620_43736 = t  in
          let uu____43737 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____43742 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____43747 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____43750 =
            FStar_List.map
              (fun uu____43778  ->
                 match uu____43778 with
                 | (t1,imp) ->
                     let uu____43797 = subst' s t1  in
                     let uu____43798 = subst_imp' s imp  in
                     (uu____43797, uu____43798))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____43803 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____43737;
            FStar_Syntax_Syntax.effect_name = uu____43742;
            FStar_Syntax_Syntax.result_typ = uu____43747;
            FStar_Syntax_Syntax.effect_args = uu____43750;
            FStar_Syntax_Syntax.flags = uu____43803
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
      | uu____43834 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____43855 = subst' s t1  in
               let uu____43856 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____43855 uu____43856
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____43873 = subst' s t1  in
               let uu____43874 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____43873 uu____43874
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____43882 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____43882)

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
          let uu____43900 =
            let uu____43901 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____43901  in
          FStar_Pervasives_Native.Some uu____43900
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
      | FStar_Syntax_Syntax.NT uu____43940 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____43967 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43967) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43967)
  =
  fun n1  ->
    fun s  ->
      let uu____43998 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____43998, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____44041  ->
      match uu____44041 with
      | (x,imp) ->
          let uu____44068 =
            let uu___679_44069 = x  in
            let uu____44070 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_44069.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_44069.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____44070
            }  in
          let uu____44073 = subst_imp' s imp  in (uu____44068, uu____44073)
  
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
                  (let uu____44179 = shift_subst' i s  in
                   subst_binder' uu____44179 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____44218 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44218) ->
        (FStar_Syntax_Syntax.term * 'Auu____44218)
  =
  fun s  ->
    fun uu____44236  ->
      match uu____44236 with
      | (t,imp) -> let uu____44243 = subst' s t  in (uu____44243, imp)
  
let subst_args' :
  'Auu____44250 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44250) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____44250) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____44344 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____44366 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____44428  ->
                      fun uu____44429  ->
                        match (uu____44428, uu____44429) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____44525 = aux n2 p2  in
                            (match uu____44525 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____44366 with
             | (pats1,n2) ->
                 ((let uu___716_44599 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_44599.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_44625 = x  in
              let uu____44626 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_44625.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_44625.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44626
              }  in
            ((let uu___724_44631 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_44631.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_44644 = x  in
              let uu____44645 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_44644.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_44644.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44645
              }  in
            ((let uu___732_44650 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_44650.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_44668 = x  in
              let uu____44669 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_44668.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_44668.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44669
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_44675 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_44675.FStar_Syntax_Syntax.p)
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
          let uu____44701 =
            let uu___750_44702 = rc  in
            let uu____44703 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_44702.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____44703;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_44702.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____44701
  
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
               (fun uu____44753  ->
                  match uu____44753 with
                  | (x',uu____44762) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_44778 =
          match uu___398_44778 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_44809  ->
                        match uu___397_44809 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____44818 = should_retain x  in
                            if uu____44818
                            then
                              let uu____44823 =
                                let uu____44824 =
                                  let uu____44831 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____44831)  in
                                FStar_Syntax_Syntax.NT uu____44824  in
                              [uu____44823]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____44846 = should_retain x  in
                            if uu____44846
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_44854 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_44854.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_44854.FStar_Syntax_Syntax.sort)
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
                               | uu____44864 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____44869 -> []))
                 in
              let uu____44870 = aux rest  in
              FStar_List.append hd1 uu____44870
           in
        let uu____44873 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____44873 with
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
        let uu____44936 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____44936
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____44939 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____44968 ->
               let t1 =
                 let uu____44978 =
                   let uu____44987 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____44987  in
                 uu____44978 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____45037 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____45038 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____45043 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____45070 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____45070 with
           | FStar_Pervasives_Native.None  ->
               let uu____45075 =
                 let uu___810_45078 = t  in
                 let uu____45081 =
                   let uu____45082 =
                     let uu____45095 = compose_uvar_subst uv s0 s  in
                     (uv, uu____45095)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____45082  in
                 {
                   FStar_Syntax_Syntax.n = uu____45081;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_45078.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_45078.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____45075 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____45119 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____45120 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____45121 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____45135 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____45135 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____45168 =
            let uu____45169 =
              let uu____45186 = subst' s t0  in
              let uu____45189 = subst_args' s args  in
              (uu____45186, uu____45189)  in
            FStar_Syntax_Syntax.Tm_app uu____45169  in
          mk1 uu____45168
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____45290 = subst' s t1  in FStar_Util.Inl uu____45290
            | FStar_Util.Inr c ->
                let uu____45304 = subst_comp' s c  in
                FStar_Util.Inr uu____45304
             in
          let uu____45311 =
            let uu____45312 =
              let uu____45339 = subst' s t0  in
              let uu____45342 =
                let uu____45359 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____45359)  in
              (uu____45339, uu____45342, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____45312  in
          mk1 uu____45311
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____45445 =
            let uu____45446 =
              let uu____45465 = subst_binders' s bs  in
              let uu____45474 = subst' s' body  in
              let uu____45477 = push_subst_lcomp s' lopt  in
              (uu____45465, uu____45474, uu____45477)  in
            FStar_Syntax_Syntax.Tm_abs uu____45446  in
          mk1 uu____45445
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____45521 =
            let uu____45522 =
              let uu____45537 = subst_binders' s bs  in
              let uu____45546 =
                let uu____45549 = shift_subst' n1 s  in
                subst_comp' uu____45549 comp  in
              (uu____45537, uu____45546)  in
            FStar_Syntax_Syntax.Tm_arrow uu____45522  in
          mk1 uu____45521
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_45579 = x  in
            let uu____45580 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_45579.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_45579.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____45580
            }  in
          let phi1 =
            let uu____45584 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____45584 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____45700  ->
                    match uu____45700 with
                    | (pat,wopt,branch) ->
                        let uu____45730 = subst_pat' s pat  in
                        (match uu____45730 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____45761 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____45761
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
                      let uu____45833 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____45833
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_45851 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_45851.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_45851.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_45853 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_45853.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_45853.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_45853.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_45853.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____45884 =
            let uu____45885 =
              let uu____45892 = subst' s t0  in
              let uu____45895 =
                let uu____45896 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____45896  in
              (uu____45892, uu____45895)  in
            FStar_Syntax_Syntax.Tm_meta uu____45885  in
          mk1 uu____45884
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____45962 =
            let uu____45963 =
              let uu____45970 = subst' s t0  in
              let uu____45973 =
                let uu____45974 =
                  let uu____45981 = subst' s t1  in (m, uu____45981)  in
                FStar_Syntax_Syntax.Meta_monadic uu____45974  in
              (uu____45970, uu____45973)  in
            FStar_Syntax_Syntax.Tm_meta uu____45963  in
          mk1 uu____45962
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____46000 =
            let uu____46001 =
              let uu____46008 = subst' s t0  in
              let uu____46011 =
                let uu____46012 =
                  let uu____46021 = subst' s t1  in (m1, m2, uu____46021)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____46012  in
              (uu____46008, uu____46011)  in
            FStar_Syntax_Syntax.Tm_meta uu____46001  in
          mk1 uu____46000
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____46036 =
                 let uu____46037 =
                   let uu____46044 = subst' s tm  in (uu____46044, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____46037  in
               mk1 uu____46036
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____46058 =
            let uu____46059 =
              let uu____46066 = subst' s t1  in (uu____46066, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____46059  in
          mk1 uu____46058
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____46080 = force_uvar t1  in
    match uu____46080 with
    | (t2,uu____46089) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____46142 =
                 let uu____46147 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____46147  in
               FStar_ST.op_Colon_Equals memo uu____46142);
              compress t2)
         | uu____46201 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____46236 =
        let uu____46237 =
          let uu____46238 =
            let uu____46239 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____46239  in
          FStar_Syntax_Syntax.SomeUseRange uu____46238  in
        ([], uu____46237)  in
      subst' uu____46236 t
  
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
    let uu____46300 =
      FStar_List.fold_right
        (fun uu____46327  ->
           fun uu____46328  ->
             match (uu____46327, uu____46328) with
             | ((x,uu____46363),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____46300 FStar_Pervasives_Native.fst
  
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
            let uu___972_46521 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____46522 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_46521.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_46521.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____46522
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____46529 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____46529
             in
          let uu____46535 = aux bs' o1  in
          (match uu____46535 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____46596 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____46596
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____46634 = open_binders' bs  in
      match uu____46634 with
      | (bs',opening) ->
          let uu____46671 = subst opening t  in (bs', uu____46671, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____46687 = open_term' bs t  in
      match uu____46687 with | (b,t1,uu____46700) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____46716 = open_binders' bs  in
      match uu____46716 with
      | (bs',opening) ->
          let uu____46751 = subst_comp opening t  in (bs', uu____46751)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____46801 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____46826 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____46897  ->
                    fun uu____46898  ->
                      match (uu____46897, uu____46898) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47012 = open_pat_aux sub2 p2  in
                          (match uu____47012 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____46826 with
           | (pats1,sub2) ->
               ((let uu___1019_47122 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_47122.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_47143 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47144 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_47143.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_47143.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47144
            }  in
          let sub2 =
            let uu____47150 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47150
             in
          ((let uu___1027_47161 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_47161.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_47166 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47167 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_47166.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_47166.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47167
            }  in
          let sub2 =
            let uu____47173 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47173
             in
          ((let uu___1035_47184 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_47184.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_47194 = x  in
            let uu____47195 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_47194.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_47194.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47195
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_47204 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_47204.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____47218  ->
    match uu____47218 with
    | (p,wopt,e) ->
        let uu____47242 = open_pat p  in
        (match uu____47242 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47271 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____47271
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____47291 = open_branch' br  in
    match uu____47291 with | (br1,uu____47297) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____47309 = closing_subst bs  in subst uu____47309 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____47323 = closing_subst bs  in subst_comp uu____47323 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_47391 = x  in
            let uu____47392 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_47391.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_47391.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47392
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____47399 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47399
             in
          let uu____47405 = aux s' tl1  in (x1, imp1) :: uu____47405
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
        (fun uu____47432  ->
           let uu____47433 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____47433)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____47487 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____47512 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____47583  ->
                    fun uu____47584  ->
                      match (uu____47583, uu____47584) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47698 = aux sub2 p2  in
                          (match uu____47698 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____47512 with
           | (pats1,sub2) ->
               ((let uu___1108_47808 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_47808.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_47829 = x  in
            let uu____47830 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_47829.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_47829.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47830
            }  in
          let sub2 =
            let uu____47836 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47836
             in
          ((let uu___1116_47847 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_47847.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_47852 = x  in
            let uu____47853 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_47852.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_47852.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47853
            }  in
          let sub2 =
            let uu____47859 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47859
             in
          ((let uu___1124_47870 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_47870.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_47880 = x  in
            let uu____47881 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_47880.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_47880.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47881
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_47890 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_47890.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____47900  ->
    match uu____47900 with
    | (p,wopt,e) ->
        let uu____47920 = close_pat p  in
        (match uu____47920 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47957 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____47957
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
      let uu____48045 = univ_var_opening us  in
      match uu____48045 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____48088 = univ_var_opening us  in
      match uu____48088 with
      | (s,us') -> let uu____48111 = subst_comp s c  in (us', uu____48111)
  
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
      let uu____48174 =
        let uu____48186 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48186
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48226  ->
                 match uu____48226 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____48263 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____48263  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_48271 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_48271.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____48174 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____48314 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48344  ->
                             match uu____48344 with
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
                    match uu____48314 with
                    | (uu____48393,us,u_let_rec_opening) ->
                        let uu___1203_48406 = lb  in
                        let uu____48407 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48410 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_48406.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____48407;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_48406.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48410;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_48406.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_48406.FStar_Syntax_Syntax.lbpos)
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
      let uu____48437 =
        let uu____48445 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48445
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48474  ->
                 match uu____48474 with
                 | (i,out) ->
                     let uu____48497 =
                       let uu____48500 =
                         let uu____48501 =
                           let uu____48507 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____48507, i)  in
                         FStar_Syntax_Syntax.NM uu____48501  in
                       uu____48500 :: out  in
                     ((i + (Prims.parse_int "1")), uu____48497)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____48437 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____48546 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48566  ->
                             match uu____48566 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____48546 with
                    | (uu____48597,u_let_rec_closing) ->
                        let uu___1225_48605 = lb  in
                        let uu____48606 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48609 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_48605.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_48605.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____48606;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_48605.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48609;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_48605.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_48605.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____48625  ->
      match uu____48625 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____48660  ->
                   match uu____48660 with
                   | (x,uu____48669) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____48696  ->
      match uu____48696 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____48726 = subst s t  in (us', uu____48726)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____48745  ->
      match uu____48745 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____48759 = subst s1 t  in (us, uu____48759)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____48800  ->
              match uu____48800 with
              | (x,uu____48809) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____48836 = open_term [b] t  in
      match uu____48836 with
      | (b1::[],t1) -> (b1, t1)
      | uu____48877 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____48908 =
        let uu____48913 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____48913 t  in
      match uu____48908 with
      | (bs,t1) ->
          let uu____48928 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____48928, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____48956 = open_term_bvs [bv] t  in
      match uu____48956 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____48971 -> failwith "impossible: open_term_bv"
  