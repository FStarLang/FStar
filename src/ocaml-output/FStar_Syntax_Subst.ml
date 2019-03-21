open Prims
let subst_to_string :
  'Auu____37826 .
    (FStar_Syntax_Syntax.bv * 'Auu____37826) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____37845 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____37866  ->
              match uu____37866 with
              | (b,uu____37873) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____37845 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____37888 'Auu____37889 .
    ('Auu____37888 -> 'Auu____37889 FStar_Pervasives_Native.option) ->
      'Auu____37888 Prims.list ->
        ('Auu____37888 Prims.list * 'Auu____37889)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____37931 = f s0  in
          (match uu____37931 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____37964 'Auu____37965 'Auu____37966 .
    ('Auu____37964 -> 'Auu____37965 -> 'Auu____37966) ->
      'Auu____37966 ->
        ('Auu____37964 * 'Auu____37965) FStar_Pervasives_Native.option ->
          'Auu____37966
  =
  fun f  ->
    fun x  ->
      fun uu___391_37993  ->
        match uu___391_37993 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____38029 'Auu____38030 'Auu____38031 .
    ('Auu____38029 -> 'Auu____38030 FStar_Pervasives_Native.option) ->
      'Auu____38029 Prims.list ->
        ('Auu____38029 Prims.list -> 'Auu____38030 -> 'Auu____38031) ->
          'Auu____38031 -> 'Auu____38031
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____38079 = apply_until_some f s  in
          FStar_All.pipe_right uu____38079 (map_some_curry g t)
  
let compose_subst :
  'Auu____38105 .
    ('Auu____38105 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____38105 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____38105 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____38156 ->
            FStar_Pervasives_Native.snd s2
        | uu____38159 -> FStar_Pervasives_Native.snd s1  in
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
      | uu____38242 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____38268;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____38269;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____38270;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____38271;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____38272;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____38273;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____38274;_},s)
        ->
        let uu____38323 = FStar_Syntax_Unionfind.find uv  in
        (match uu____38323 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____38334 =
               let uu____38337 =
                 let uu____38345 = delay t' s  in force_uvar' uu____38345  in
               FStar_Pervasives_Native.fst uu____38337  in
             (uu____38334, true)
         | uu____38355 -> (t, false))
    | uu____38362 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____38384 = force_uvar' t  in
    match uu____38384 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____38420 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____38420, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____38494 = FStar_ST.op_Bang m  in
        (match uu____38494 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____38544 = try_read_memo_aux t'  in
             (match uu____38544 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____38604 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____38621 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____38621
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____38647 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____38647 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____38651 -> u)
    | uu____38654 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_38676  ->
           match uu___392_38676 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____38684 =
                 let uu____38685 =
                   let uu____38686 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____38686  in
                 FStar_Syntax_Syntax.bv_to_name uu____38685  in
               FStar_Pervasives_Native.Some uu____38684
           | uu____38687 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_38713  ->
           match uu___393_38713 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____38722 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_38727 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_38727.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_38727.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____38722
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____38738 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_38763  ->
           match uu___394_38763 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____38771 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_38792  ->
           match uu___395_38792 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____38800 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____38828 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____38838 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____38838
      | FStar_Syntax_Syntax.U_max us ->
          let uu____38842 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____38842
  
let tag_with_range :
  'Auu____38852 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____38852 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____38878 =
            let uu____38880 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____38881 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____38880 uu____38881  in
          if uu____38878
          then t
          else
            (let r1 =
               let uu____38888 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____38888
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____38891 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____38891
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____38893 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____38893
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_38899 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____38900 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____38900;
                       FStar_Syntax_Syntax.p =
                         (uu___551_38899.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_38902 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_38902.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_38902.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_38904 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_38904.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____38914 .
    FStar_Ident.lident ->
      ('Auu____38914 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____38934 =
            let uu____38936 =
              let uu____38937 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____38937  in
            let uu____38938 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____38936 uu____38938  in
          if uu____38934
          then l
          else
            (let uu____38942 =
               let uu____38943 = FStar_Ident.range_of_lid l  in
               let uu____38944 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____38943 uu____38944  in
             FStar_Ident.set_lid_range l uu____38942)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____38961 =
            let uu____38963 = FStar_Range.use_range r  in
            let uu____38964 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____38963 uu____38964  in
          if uu____38961
          then r
          else
            (let uu____38968 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____38968)
  
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
      | uu____39089 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____39097 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____39102 -> tag_with_range t0 s
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
               let uu____39171 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____39172 =
                 let uu____39179 =
                   let uu____39180 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____39180  in
                 FStar_Syntax_Syntax.mk uu____39179  in
               uu____39172 FStar_Pervasives_Native.None uu____39171
           | uu____39185 ->
               let uu____39186 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____39186)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_39198  ->
              match uu___396_39198 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____39202 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____39202
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
      | uu____39230 ->
          let uu___620_39239 = t  in
          let uu____39240 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____39245 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____39250 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____39253 =
            FStar_List.map
              (fun uu____39281  ->
                 match uu____39281 with
                 | (t1,imp) ->
                     let uu____39300 = subst' s t1  in
                     let uu____39301 = subst_imp' s imp  in
                     (uu____39300, uu____39301))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____39306 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____39240;
            FStar_Syntax_Syntax.effect_name = uu____39245;
            FStar_Syntax_Syntax.result_typ = uu____39250;
            FStar_Syntax_Syntax.effect_args = uu____39253;
            FStar_Syntax_Syntax.flags = uu____39306
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
      | uu____39337 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____39358 = subst' s t1  in
               let uu____39359 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____39358 uu____39359
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____39376 = subst' s t1  in
               let uu____39377 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____39376 uu____39377
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____39385 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____39385)

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
          let uu____39403 =
            let uu____39404 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____39404  in
          FStar_Pervasives_Native.Some uu____39403
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
      | FStar_Syntax_Syntax.NT uu____39443 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____39470 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____39470) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____39470)
  =
  fun n1  ->
    fun s  ->
      let uu____39501 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____39501, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____39544  ->
      match uu____39544 with
      | (x,imp) ->
          let uu____39571 =
            let uu___679_39572 = x  in
            let uu____39573 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_39572.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_39572.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____39573
            }  in
          let uu____39576 = subst_imp' s imp  in (uu____39571, uu____39576)
  
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
                  (let uu____39682 = shift_subst' i s  in
                   subst_binder' uu____39682 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____39721 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____39721) ->
        (FStar_Syntax_Syntax.term * 'Auu____39721)
  =
  fun s  ->
    fun uu____39739  ->
      match uu____39739 with
      | (t,imp) -> let uu____39746 = subst' s t  in (uu____39746, imp)
  
let subst_args' :
  'Auu____39753 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____39753) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____39753) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____39847 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____39869 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____39931  ->
                      fun uu____39932  ->
                        match (uu____39931, uu____39932) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____40028 = aux n2 p2  in
                            (match uu____40028 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____39869 with
             | (pats1,n2) ->
                 ((let uu___716_40102 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_40102.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_40128 = x  in
              let uu____40129 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_40128.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_40128.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40129
              }  in
            ((let uu___724_40134 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_40134.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_40147 = x  in
              let uu____40148 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_40147.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_40147.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40148
              }  in
            ((let uu___732_40153 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_40153.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_40171 = x  in
              let uu____40172 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_40171.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_40171.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____40172
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_40178 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_40178.FStar_Syntax_Syntax.p)
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
          let uu____40204 =
            let uu___750_40205 = rc  in
            let uu____40206 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_40205.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____40206;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_40205.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____40204
  
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
               (fun uu____40256  ->
                  match uu____40256 with
                  | (x',uu____40265) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_40281 =
          match uu___398_40281 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_40312  ->
                        match uu___397_40312 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____40321 = should_retain x  in
                            if uu____40321
                            then
                              let uu____40326 =
                                let uu____40327 =
                                  let uu____40334 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____40334)  in
                                FStar_Syntax_Syntax.NT uu____40327  in
                              [uu____40326]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____40349 = should_retain x  in
                            if uu____40349
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_40357 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_40357.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_40357.FStar_Syntax_Syntax.sort)
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
                               | uu____40367 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____40372 -> []))
                 in
              let uu____40373 = aux rest  in
              FStar_List.append hd1 uu____40373
           in
        let uu____40376 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____40376 with
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
        let uu____40439 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____40439
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____40442 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____40471 ->
               let t1 =
                 let uu____40481 =
                   let uu____40490 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____40490  in
                 uu____40481 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____40540 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____40541 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____40546 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____40573 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____40573 with
           | FStar_Pervasives_Native.None  ->
               let uu____40578 =
                 let uu___810_40581 = t  in
                 let uu____40584 =
                   let uu____40585 =
                     let uu____40598 = compose_uvar_subst uv s0 s  in
                     (uv, uu____40598)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____40585  in
                 {
                   FStar_Syntax_Syntax.n = uu____40584;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_40581.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_40581.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____40578 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____40622 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____40623 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____40624 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____40638 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____40638 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____40671 =
            let uu____40672 =
              let uu____40689 = subst' s t0  in
              let uu____40692 = subst_args' s args  in
              (uu____40689, uu____40692)  in
            FStar_Syntax_Syntax.Tm_app uu____40672  in
          mk1 uu____40671
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____40793 = subst' s t1  in FStar_Util.Inl uu____40793
            | FStar_Util.Inr c ->
                let uu____40807 = subst_comp' s c  in
                FStar_Util.Inr uu____40807
             in
          let uu____40814 =
            let uu____40815 =
              let uu____40842 = subst' s t0  in
              let uu____40845 =
                let uu____40862 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____40862)  in
              (uu____40842, uu____40845, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____40815  in
          mk1 uu____40814
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____40944 =
            let uu____40945 =
              let uu____40964 = subst_binders' s bs  in
              let uu____40973 = subst' s' body  in
              let uu____40976 = push_subst_lcomp s' lopt  in
              (uu____40964, uu____40973, uu____40976)  in
            FStar_Syntax_Syntax.Tm_abs uu____40945  in
          mk1 uu____40944
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____41020 =
            let uu____41021 =
              let uu____41036 = subst_binders' s bs  in
              let uu____41045 =
                let uu____41048 = shift_subst' n1 s  in
                subst_comp' uu____41048 comp  in
              (uu____41036, uu____41045)  in
            FStar_Syntax_Syntax.Tm_arrow uu____41021  in
          mk1 uu____41020
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_41074 = x  in
            let uu____41075 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_41074.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_41074.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____41075
            }  in
          let phi1 =
            let uu____41079 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____41079 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____41195  ->
                    match uu____41195 with
                    | (pat,wopt,branch) ->
                        let uu____41225 = subst_pat' s pat  in
                        (match uu____41225 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____41256 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____41256
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
                      let uu____41324 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____41324
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_41342 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_41342.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_41342.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_41344 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_41344.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_41344.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_41344.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_41344.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____41375 =
            let uu____41376 =
              let uu____41383 = subst' s t0  in
              let uu____41386 =
                let uu____41387 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____41387  in
              (uu____41383, uu____41386)  in
            FStar_Syntax_Syntax.Tm_meta uu____41376  in
          mk1 uu____41375
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____41453 =
            let uu____41454 =
              let uu____41461 = subst' s t0  in
              let uu____41464 =
                let uu____41465 =
                  let uu____41472 = subst' s t1  in (m, uu____41472)  in
                FStar_Syntax_Syntax.Meta_monadic uu____41465  in
              (uu____41461, uu____41464)  in
            FStar_Syntax_Syntax.Tm_meta uu____41454  in
          mk1 uu____41453
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____41491 =
            let uu____41492 =
              let uu____41499 = subst' s t0  in
              let uu____41502 =
                let uu____41503 =
                  let uu____41512 = subst' s t1  in (m1, m2, uu____41512)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____41503  in
              (uu____41499, uu____41502)  in
            FStar_Syntax_Syntax.Tm_meta uu____41492  in
          mk1 uu____41491
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____41527 =
                 let uu____41528 =
                   let uu____41535 = subst' s tm  in (uu____41535, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____41528  in
               mk1 uu____41527
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____41549 =
            let uu____41550 =
              let uu____41557 = subst' s t1  in (uu____41557, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____41550  in
          mk1 uu____41549
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____41571 = force_uvar t1  in
    match uu____41571 with
    | (t2,uu____41580) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____41633 =
                 let uu____41638 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____41638  in
               FStar_ST.op_Colon_Equals memo uu____41633);
              compress t2)
         | uu____41670 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____41705 =
        let uu____41706 =
          let uu____41707 =
            let uu____41708 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____41708  in
          FStar_Syntax_Syntax.SomeUseRange uu____41707  in
        ([], uu____41706)  in
      subst' uu____41705 t
  
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
    let uu____41769 =
      FStar_List.fold_right
        (fun uu____41796  ->
           fun uu____41797  ->
             match (uu____41796, uu____41797) with
             | ((x,uu____41832),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____41769 FStar_Pervasives_Native.fst
  
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
            let uu___972_41990 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____41991 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_41990.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_41990.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____41991
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____41998 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____41998
             in
          let uu____42004 = aux bs' o1  in
          (match uu____42004 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____42065 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____42065
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____42103 = open_binders' bs  in
      match uu____42103 with
      | (bs',opening) ->
          let uu____42140 = subst opening t  in (bs', uu____42140, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____42156 = open_term' bs t  in
      match uu____42156 with | (b,t1,uu____42169) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____42185 = open_binders' bs  in
      match uu____42185 with
      | (bs',opening) ->
          let uu____42220 = subst_comp opening t  in (bs', uu____42220)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____42270 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____42295 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____42366  ->
                    fun uu____42367  ->
                      match (uu____42366, uu____42367) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____42481 = open_pat_aux sub2 p2  in
                          (match uu____42481 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____42295 with
           | (pats1,sub2) ->
               ((let uu___1019_42591 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_42591.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_42612 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____42613 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_42612.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_42612.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42613
            }  in
          let sub2 =
            let uu____42619 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____42619
             in
          ((let uu___1027_42630 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_42630.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_42635 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____42636 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_42635.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_42635.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42636
            }  in
          let sub2 =
            let uu____42642 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____42642
             in
          ((let uu___1035_42653 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_42653.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_42663 = x  in
            let uu____42664 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_42663.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_42663.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42664
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_42673 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_42673.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____42687  ->
    match uu____42687 with
    | (p,wopt,e) ->
        let uu____42711 = open_pat p  in
        (match uu____42711 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____42740 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____42740
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____42760 = open_branch' br  in
    match uu____42760 with | (br1,uu____42766) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____42778 = closing_subst bs  in subst uu____42778 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____42792 = closing_subst bs  in subst_comp uu____42792 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_42860 = x  in
            let uu____42861 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_42860.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_42860.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42861
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____42868 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____42868
             in
          let uu____42874 = aux s' tl1  in (x1, imp1) :: uu____42874
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
        (fun uu____42901  ->
           let uu____42902 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____42902)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____42956 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____42981 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____43052  ->
                    fun uu____43053  ->
                      match (uu____43052, uu____43053) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____43167 = aux sub2 p2  in
                          (match uu____43167 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____42981 with
           | (pats1,sub2) ->
               ((let uu___1108_43277 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_43277.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_43298 = x  in
            let uu____43299 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_43298.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_43298.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43299
            }  in
          let sub2 =
            let uu____43305 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43305
             in
          ((let uu___1116_43316 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_43316.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_43321 = x  in
            let uu____43322 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_43321.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_43321.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43322
            }  in
          let sub2 =
            let uu____43328 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____43328
             in
          ((let uu___1124_43339 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_43339.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_43349 = x  in
            let uu____43350 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_43349.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_43349.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____43350
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_43359 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_43359.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____43369  ->
    match uu____43369 with
    | (p,wopt,e) ->
        let uu____43389 = close_pat p  in
        (match uu____43389 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____43426 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____43426
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
      let uu____43514 = univ_var_opening us  in
      match uu____43514 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____43557 = univ_var_opening us  in
      match uu____43557 with
      | (s,us') -> let uu____43580 = subst_comp s c  in (us', uu____43580)
  
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
      let uu____43643 =
        let uu____43655 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____43655
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____43695  ->
                 match uu____43695 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____43732 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____43732  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_43740 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_43740.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____43643 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____43783 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____43813  ->
                             match uu____43813 with
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
                    match uu____43783 with
                    | (uu____43862,us,u_let_rec_opening) ->
                        let uu___1203_43875 = lb  in
                        let uu____43876 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____43879 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_43875.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____43876;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_43875.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____43879;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_43875.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_43875.FStar_Syntax_Syntax.lbpos)
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
      let uu____43906 =
        let uu____43914 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____43914
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____43943  ->
                 match uu____43943 with
                 | (i,out) ->
                     let uu____43966 =
                       let uu____43969 =
                         let uu____43970 =
                           let uu____43976 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____43976, i)  in
                         FStar_Syntax_Syntax.NM uu____43970  in
                       uu____43969 :: out  in
                     ((i + (Prims.parse_int "1")), uu____43966)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____43906 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____44015 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____44035  ->
                             match uu____44035 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____44015 with
                    | (uu____44066,u_let_rec_closing) ->
                        let uu___1225_44074 = lb  in
                        let uu____44075 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____44078 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_44074.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_44074.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____44075;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_44074.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____44078;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_44074.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_44074.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____44094  ->
      match uu____44094 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____44129  ->
                   match uu____44129 with
                   | (x,uu____44138) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____44159  ->
      match uu____44159 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____44183 = subst s t  in (us', uu____44183)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____44202  ->
      match uu____44202 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____44216 = subst s1 t  in (us, uu____44216)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____44257  ->
              match uu____44257 with
              | (x,uu____44266) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____44293 = open_term [b] t  in
      match uu____44293 with
      | (b1::[],t1) -> (b1, t1)
      | uu____44334 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____44365 =
        let uu____44370 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____44370 t  in
      match uu____44365 with
      | (bs,t1) ->
          let uu____44385 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____44385, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____44413 = open_term_bvs [bv] t  in
      match uu____44413 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____44428 -> failwith "impossible: open_term_bv"
  