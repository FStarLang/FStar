open Prims
let subst_to_string :
  'Auu____37811 .
    (FStar_Syntax_Syntax.bv * 'Auu____37811) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____37830 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____37851  ->
              match uu____37851 with
              | (b,uu____37858) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____37830 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____37873 'Auu____37874 .
    ('Auu____37873 -> 'Auu____37874 FStar_Pervasives_Native.option) ->
      'Auu____37873 Prims.list ->
        ('Auu____37873 Prims.list * 'Auu____37874)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____37916 = f s0  in
          (match uu____37916 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____37949 'Auu____37950 'Auu____37951 .
    ('Auu____37949 -> 'Auu____37950 -> 'Auu____37951) ->
      'Auu____37951 ->
        ('Auu____37949 * 'Auu____37950) FStar_Pervasives_Native.option ->
          'Auu____37951
  =
  fun f  ->
    fun x  ->
      fun uu___391_37978  ->
        match uu___391_37978 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____38014 'Auu____38015 'Auu____38016 .
    ('Auu____38014 -> 'Auu____38015 FStar_Pervasives_Native.option) ->
      'Auu____38014 Prims.list ->
        ('Auu____38014 Prims.list -> 'Auu____38015 -> 'Auu____38016) ->
          'Auu____38016 -> 'Auu____38016
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____38064 = apply_until_some f s  in
          FStar_All.pipe_right uu____38064 (map_some_curry g t)
  
let compose_subst :
  'Auu____38090 .
    ('Auu____38090 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____38090 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____38090 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____38141 ->
            FStar_Pervasives_Native.snd s2
        | uu____38144 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____38227 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____38253;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____38254;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____38255;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____38256;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____38257;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____38258;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____38259;_},s)
        ->
        let uu____38308 = FStar_Syntax_Unionfind.find uv  in
        (match uu____38308 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____38319 =
               let uu____38322 =
                 let uu____38330 = delay t' s  in force_uvar' uu____38330  in
               FStar_Pervasives_Native.fst uu____38322  in
             (uu____38319, true)
         | uu____38340 -> (t, false))
    | uu____38347 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____38369 = force_uvar' t  in
    match uu____38369 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____38405 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____38405, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____38479 = FStar_ST.op_Bang m  in
        (match uu____38479 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____38529 = try_read_memo_aux t'  in
             (match uu____38529 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____38589 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____38606 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____38606
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____38632 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____38632 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____38636 -> u)
    | uu____38639 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_38661  ->
           match uu___392_38661 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____38669 =
                 let uu____38670 =
                   let uu____38671 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____38671  in
                 FStar_Syntax_Syntax.bv_to_name uu____38670  in
               FStar_Pervasives_Native.Some uu____38669
           | uu____38672 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_38698  ->
           match uu___393_38698 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____38707 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_38712 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_38712.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_38712.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____38707
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____38723 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_38748  ->
           match uu___394_38748 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____38756 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_38777  ->
           match uu___395_38777 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____38785 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____38813 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____38823 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____38823
      | FStar_Syntax_Syntax.U_max us ->
          let uu____38827 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____38827
  
let tag_with_range :
  'Auu____38837 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____38837 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____38863 =
            let uu____38865 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____38866 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____38865 uu____38866  in
          if uu____38863
          then t
          else
            (let r1 =
               let uu____38873 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____38873
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____38876 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____38876
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____38878 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____38878
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_38884 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____38885 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____38885;
                       FStar_Syntax_Syntax.p =
                         (uu___551_38884.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_38887 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_38887.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_38887.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_38889 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_38889.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____38899 .
    FStar_Ident.lident ->
      ('Auu____38899 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____38919 =
            let uu____38921 =
              let uu____38922 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____38922  in
            let uu____38923 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____38921 uu____38923  in
          if uu____38919
          then l
          else
            (let uu____38927 =
               let uu____38928 = FStar_Ident.range_of_lid l  in
               let uu____38929 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____38928 uu____38929  in
             FStar_Ident.set_lid_range l uu____38927)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____38946 =
            let uu____38948 = FStar_Range.use_range r  in
            let uu____38949 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____38948 uu____38949  in
          if uu____38946
          then r
          else
            (let uu____38953 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____38953)
  
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
      | uu____39074 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____39082 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____39087 -> tag_with_range t0 s
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
               let uu____39156 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____39157 =
                 let uu____39164 =
                   let uu____39165 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____39165  in
                 FStar_Syntax_Syntax.mk uu____39164  in
               uu____39157 FStar_Pervasives_Native.None uu____39156
           | uu____39170 ->
               let uu____39171 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____39171)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_39183  ->
              match uu___396_39183 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____39187 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____39187
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
      | uu____39215 ->
          let uu___620_39224 = t  in
          let uu____39225 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____39230 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____39235 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____39238 =
            FStar_List.map
              (fun uu____39266  ->
                 match uu____39266 with
                 | (t1,imp) ->
                     let uu____39285 = subst' s t1  in
                     let uu____39286 = subst_imp' s imp  in
                     (uu____39285, uu____39286))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____39291 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____39225;
            FStar_Syntax_Syntax.effect_name = uu____39230;
            FStar_Syntax_Syntax.result_typ = uu____39235;
            FStar_Syntax_Syntax.effect_args = uu____39238;
            FStar_Syntax_Syntax.flags = uu____39291
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
      | uu____39322 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____39343 = subst' s t1  in
               let uu____39344 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____39343 uu____39344
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____39361 = subst' s t1  in
               let uu____39362 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____39361 uu____39362
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____39370 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____39370)

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
          let uu____39388 =
            let uu____39389 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____39389  in
          FStar_Pervasives_Native.Some uu____39388
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
      | FStar_Syntax_Syntax.NT uu____39428 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____39455 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____39455) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____39455)
  =
  fun n1  ->
    fun s  ->
      let uu____39486 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____39486, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____39529  ->
      match uu____39529 with
      | (x,imp) ->
          let uu____39556 =
            let uu___679_39557 = x  in
            let uu____39558 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_39557.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_39557.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____39558
            }  in
          let uu____39561 = subst_imp' s imp  in (uu____39556, uu____39561)
  
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
                  (let uu____39667 = shift_subst' i s  in
                   subst_binder' uu____39667 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____39706 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____39706) ->
        (FStar_Syntax_Syntax.term * 'Auu____39706)
  =
  fun s  ->
    fun uu____39724  ->
      match uu____39724 with
      | (t,imp) -> let uu____39731 = subst' s t  in (uu____39731, imp)
  
let subst_args' :
  'Auu____39738 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____39738) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____39738) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____39832 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____39854 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____39916  ->
                      fun uu____39917  ->
                        match (uu____39916, uu____39917) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____40013 = aux n2 p2  in
                            (match uu____40013 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____39854 with
             | (pats1,n2) ->
                 ((let uu___716_40087 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_40087.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_40113 = x  in
              let uu____40114 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_40113.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_40113.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40114
              }  in
            ((let uu___724_40119 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_40119.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_40132 = x  in
              let uu____40133 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_40132.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_40132.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40133
              }  in
            ((let uu___732_40138 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_40138.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_40156 = x  in
              let uu____40157 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_40156.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_40156.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40157
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_40163 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_40163.FStar_Syntax_Syntax.p)
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
          let uu____40189 =
            let uu___750_40190 = rc  in
            let uu____40191 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_40190.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____40191;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_40190.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____40189
  
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
               (fun uu____40241  ->
                  match uu____40241 with
                  | (x',uu____40250) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_40266 =
          match uu___398_40266 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_40297  ->
                        match uu___397_40297 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____40306 = should_retain x  in
                            if uu____40306
                            then
                              let uu____40311 =
                                let uu____40312 =
                                  let uu____40319 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____40319)  in
                                FStar_Syntax_Syntax.NT uu____40312  in
                              [uu____40311]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____40334 = should_retain x  in
                            if uu____40334
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_40342 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_40342.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_40342.FStar_Syntax_Syntax.sort)
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
                               | uu____40352 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____40357 -> []))
                 in
              let uu____40358 = aux rest  in
              FStar_List.append hd1 uu____40358
           in
        let uu____40361 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____40361 with
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
        let uu____40424 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____40424
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____40427 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____40456 ->
               let t1 =
                 let uu____40466 =
                   let uu____40475 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____40475  in
                 uu____40466 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____40525 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____40526 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____40531 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____40558 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____40558 with
           | FStar_Pervasives_Native.None  ->
               let uu____40563 =
                 let uu___810_40566 = t  in
                 let uu____40569 =
                   let uu____40570 =
                     let uu____40583 = compose_uvar_subst uv s0 s  in
                     (uv, uu____40583)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____40570  in
                 {
                   FStar_Syntax_Syntax.n = uu____40569;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_40566.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_40566.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____40563 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____40607 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____40608 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____40609 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____40623 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____40623 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____40656 =
            let uu____40657 =
              let uu____40674 = subst' s t0  in
              let uu____40677 = subst_args' s args  in
              (uu____40674, uu____40677)  in
            FStar_Syntax_Syntax.Tm_app uu____40657  in
          mk1 uu____40656
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____40778 = subst' s t1  in FStar_Util.Inl uu____40778
            | FStar_Util.Inr c ->
                let uu____40792 = subst_comp' s c  in
                FStar_Util.Inr uu____40792
             in
          let uu____40799 =
            let uu____40800 =
              let uu____40827 = subst' s t0  in
              let uu____40830 =
                let uu____40847 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____40847)  in
              (uu____40827, uu____40830, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____40800  in
          mk1 uu____40799
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____40929 =
            let uu____40930 =
              let uu____40949 = subst_binders' s bs  in
              let uu____40958 = subst' s' body  in
              let uu____40961 = push_subst_lcomp s' lopt  in
              (uu____40949, uu____40958, uu____40961)  in
            FStar_Syntax_Syntax.Tm_abs uu____40930  in
          mk1 uu____40929
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____41005 =
            let uu____41006 =
              let uu____41021 = subst_binders' s bs  in
              let uu____41030 =
                let uu____41033 = shift_subst' n1 s  in
                subst_comp' uu____41033 comp  in
              (uu____41021, uu____41030)  in
            FStar_Syntax_Syntax.Tm_arrow uu____41006  in
          mk1 uu____41005
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_41059 = x  in
            let uu____41060 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_41059.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_41059.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____41060
            }  in
          let phi1 =
            let uu____41064 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____41064 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____41180  ->
                    match uu____41180 with
                    | (pat,wopt,branch) ->
                        let uu____41210 = subst_pat' s pat  in
                        (match uu____41210 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____41241 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____41241
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
                      let uu____41309 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____41309
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_41327 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_41327.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_41327.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_41329 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_41329.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_41329.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_41329.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_41329.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____41360 =
            let uu____41361 =
              let uu____41368 = subst' s t0  in
              let uu____41371 =
                let uu____41372 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____41372  in
              (uu____41368, uu____41371)  in
            FStar_Syntax_Syntax.Tm_meta uu____41361  in
          mk1 uu____41360
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____41438 =
            let uu____41439 =
              let uu____41446 = subst' s t0  in
              let uu____41449 =
                let uu____41450 =
                  let uu____41457 = subst' s t1  in (m, uu____41457)  in
                FStar_Syntax_Syntax.Meta_monadic uu____41450  in
              (uu____41446, uu____41449)  in
            FStar_Syntax_Syntax.Tm_meta uu____41439  in
          mk1 uu____41438
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____41476 =
            let uu____41477 =
              let uu____41484 = subst' s t0  in
              let uu____41487 =
                let uu____41488 =
                  let uu____41497 = subst' s t1  in (m1, m2, uu____41497)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____41488  in
              (uu____41484, uu____41487)  in
            FStar_Syntax_Syntax.Tm_meta uu____41477  in
          mk1 uu____41476
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____41512 =
                 let uu____41513 =
                   let uu____41520 = subst' s tm  in (uu____41520, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____41513  in
               mk1 uu____41512
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____41534 =
            let uu____41535 =
              let uu____41542 = subst' s t1  in (uu____41542, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____41535  in
          mk1 uu____41534
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____41556 = force_uvar t1  in
    match uu____41556 with
    | (t2,uu____41565) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____41618 =
                 let uu____41623 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____41623  in
               FStar_ST.op_Colon_Equals memo uu____41618);
              compress t2)
         | uu____41655 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____41690 =
        let uu____41691 =
          let uu____41692 =
            let uu____41693 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____41693  in
          FStar_Syntax_Syntax.SomeUseRange uu____41692  in
        ([], uu____41691)  in
      subst' uu____41690 t
  
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
    let uu____41754 =
      FStar_List.fold_right
        (fun uu____41781  ->
           fun uu____41782  ->
             match (uu____41781, uu____41782) with
             | ((x,uu____41817),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____41754 FStar_Pervasives_Native.fst
  
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
            let uu___972_41975 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____41976 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_41975.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_41975.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____41976
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____41983 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____41983
             in
          let uu____41989 = aux bs' o1  in
          (match uu____41989 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____42050 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____42050
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____42088 = open_binders' bs  in
      match uu____42088 with
      | (bs',opening) ->
          let uu____42125 = subst opening t  in (bs', uu____42125, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____42141 = open_term' bs t  in
      match uu____42141 with | (b,t1,uu____42154) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____42170 = open_binders' bs  in
      match uu____42170 with
      | (bs',opening) ->
          let uu____42205 = subst_comp opening t  in (bs', uu____42205)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____42255 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____42280 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____42351  ->
                    fun uu____42352  ->
                      match (uu____42351, uu____42352) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____42466 = open_pat_aux sub2 p2  in
                          (match uu____42466 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____42280 with
           | (pats1,sub2) ->
               ((let uu___1019_42576 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_42576.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_42597 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____42598 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_42597.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_42597.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42598
            }  in
          let sub2 =
            let uu____42604 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____42604
             in
          ((let uu___1027_42615 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_42615.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_42620 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____42621 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_42620.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_42620.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42621
            }  in
          let sub2 =
            let uu____42627 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____42627
             in
          ((let uu___1035_42638 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_42638.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_42648 = x  in
            let uu____42649 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_42648.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_42648.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42649
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_42658 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_42658.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____42672  ->
    match uu____42672 with
    | (p,wopt,e) ->
        let uu____42696 = open_pat p  in
        (match uu____42696 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____42725 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____42725
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____42745 = open_branch' br  in
    match uu____42745 with | (br1,uu____42751) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____42763 = closing_subst bs  in subst uu____42763 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____42777 = closing_subst bs  in subst_comp uu____42777 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_42845 = x  in
            let uu____42846 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_42845.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_42845.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42846
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____42853 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____42853
             in
          let uu____42859 = aux s' tl1  in (x1, imp1) :: uu____42859
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
        (fun uu____42886  ->
           let uu____42887 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____42887)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____42941 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____42966 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____43037  ->
                    fun uu____43038  ->
                      match (uu____43037, uu____43038) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____43152 = aux sub2 p2  in
                          (match uu____43152 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____42966 with
           | (pats1,sub2) ->
               ((let uu___1108_43262 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_43262.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_43283 = x  in
            let uu____43284 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_43283.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_43283.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43284
            }  in
          let sub2 =
            let uu____43290 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43290
             in
          ((let uu___1116_43301 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_43301.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_43306 = x  in
            let uu____43307 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_43306.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_43306.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43307
            }  in
          let sub2 =
            let uu____43313 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43313
             in
          ((let uu___1124_43324 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_43324.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_43334 = x  in
            let uu____43335 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_43334.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_43334.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43335
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_43344 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_43344.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____43354  ->
    match uu____43354 with
    | (p,wopt,e) ->
        let uu____43374 = close_pat p  in
        (match uu____43374 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____43411 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____43411
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
      let uu____43499 = univ_var_opening us  in
      match uu____43499 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____43542 = univ_var_opening us  in
      match uu____43542 with
      | (s,us') -> let uu____43565 = subst_comp s c  in (us', uu____43565)
  
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
      let uu____43628 =
        let uu____43640 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____43640
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____43680  ->
                 match uu____43680 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____43717 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____43717  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_43725 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_43725.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____43628 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____43768 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____43798  ->
                             match uu____43798 with
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
                    match uu____43768 with
                    | (uu____43847,us,u_let_rec_opening) ->
                        let uu___1203_43860 = lb  in
                        let uu____43861 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____43864 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_43860.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____43861;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_43860.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____43864;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_43860.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_43860.FStar_Syntax_Syntax.lbpos)
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
      let uu____43891 =
        let uu____43899 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____43899
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____43928  ->
                 match uu____43928 with
                 | (i,out) ->
                     let uu____43951 =
                       let uu____43954 =
                         let uu____43955 =
                           let uu____43961 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____43961, i)  in
                         FStar_Syntax_Syntax.NM uu____43955  in
                       uu____43954 :: out  in
                     ((i + (Prims.parse_int "1")), uu____43951)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____43891 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____44000 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____44020  ->
                             match uu____44020 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____44000 with
                    | (uu____44051,u_let_rec_closing) ->
                        let uu___1225_44059 = lb  in
                        let uu____44060 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____44063 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_44059.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_44059.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____44060;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_44059.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____44063;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_44059.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_44059.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____44079  ->
      match uu____44079 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____44114  ->
                   match uu____44114 with
                   | (x,uu____44123) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____44144  ->
      match uu____44144 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____44168 = subst s t  in (us', uu____44168)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____44187  ->
      match uu____44187 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____44201 = subst s1 t  in (us, uu____44201)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____44242  ->
              match uu____44242 with
              | (x,uu____44251) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____44278 = open_term [b] t  in
      match uu____44278 with
      | (b1::[],t1) -> (b1, t1)
      | uu____44319 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____44350 =
        let uu____44355 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____44355 t  in
      match uu____44350 with
      | (bs,t1) ->
          let uu____44370 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____44370, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____44398 = open_term_bvs [bv] t  in
      match uu____44398 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____44413 -> failwith "impossible: open_term_bv"
  