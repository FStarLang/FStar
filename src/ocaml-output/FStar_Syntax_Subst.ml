open Prims
let subst_to_string :
  'uuuuuu4 . (FStar_Syntax_Syntax.bv * 'uuuuuu4) Prims.list -> Prims.string =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____44  ->
              match uu____44 with
              | (b,uu____51) ->
                  FStar_Ident.text_of_id b.FStar_Syntax_Syntax.ppname))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'uuuuuu66 'uuuuuu67 .
    ('uuuuuu66 -> 'uuuuuu67 FStar_Pervasives_Native.option) ->
      'uuuuuu66 Prims.list ->
        ('uuuuuu66 Prims.list * 'uuuuuu67) FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____109 = f s0  in
          (match uu____109 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'uuuuuu142 'uuuuuu143 'uuuuuu144 .
    ('uuuuuu142 -> 'uuuuuu143 -> 'uuuuuu144) ->
      'uuuuuu144 ->
        ('uuuuuu142 * 'uuuuuu143) FStar_Pervasives_Native.option ->
          'uuuuuu144
  =
  fun f  ->
    fun x  ->
      fun uu___0_171  ->
        match uu___0_171 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'uuuuuu207 'uuuuuu208 'uuuuuu209 .
    ('uuuuuu207 -> 'uuuuuu208 FStar_Pervasives_Native.option) ->
      'uuuuuu207 Prims.list ->
        ('uuuuuu207 Prims.list -> 'uuuuuu208 -> 'uuuuuu209) ->
          'uuuuuu209 -> 'uuuuuu209
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____257 = apply_until_some f s  in
          FStar_All.pipe_right uu____257 (map_some_curry g t)
  
let compose_subst :
  'uuuuuu283 .
    ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('uuuuuu283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____334 ->
            FStar_Pervasives_Native.snd s2
        | uu____337 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed (t',s') ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____397 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____423;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____424;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____425;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____426;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____427;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____428;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____429;_},s)
        ->
        let uu____480 = FStar_Syntax_Unionfind.find uv  in
        (match uu____480 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____491 =
               let uu____494 =
                 let uu____502 = delay t' s  in force_uvar' uu____502  in
               FStar_Pervasives_Native.fst uu____494  in
             (uu____491, true)
         | uu____512 -> (t, false))
    | uu____519 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____536 = force_uvar' t  in
    match uu____536 with
    | (t',forced) ->
        if forced
        then
          delay t'
            ([],
              (FStar_Syntax_Syntax.SomeUseRange (t.FStar_Syntax_Syntax.pos)))
        else t
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____582 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____582 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____586 -> u)
    | uu____589 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_611  ->
           match uu___1_611 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____619 =
                 let uu____620 =
                   let uu____621 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____621  in
                 FStar_Syntax_Syntax.bv_to_name uu____620  in
               FStar_Pervasives_Native.Some uu____619
           | uu____622 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_648  ->
           match uu___2_648 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____657 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___91_662 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___91_662.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___91_662.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____657
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____673 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_698  ->
           match uu___3_698 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____706 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_727  ->
           match uu___4_727 with
           | FStar_Syntax_Syntax.UD (y,i) when FStar_Ident.ident_equals x y
               -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____734 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____762 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____774 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____774
      | FStar_Syntax_Syntax.U_max us ->
          let uu____778 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____778
  
let tag_with_range :
  'uuuuuu788 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('uuuuuu788 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____814 =
            let uu____816 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____817 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____816 uu____817  in
          if uu____814
          then t
          else
            (let r1 =
               let uu____824 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____824
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____827 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____827
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____829 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____829
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v =
                     let uu___143_835 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____836 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____836;
                       FStar_Syntax_Syntax.p =
                         (uu___143_835.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___146_838 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___146_838.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___146_838.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___151_840 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___151_840.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'uuuuuu850 .
    FStar_Ident.lident ->
      ('uuuuuu850 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____870 =
            let uu____872 =
              let uu____873 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____873  in
            let uu____874 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____872 uu____874  in
          if uu____870
          then l
          else
            (let uu____878 =
               let uu____879 = FStar_Ident.range_of_lid l  in
               let uu____880 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____879 uu____880  in
             FStar_Ident.set_lid_range l uu____878)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____897 =
            let uu____899 = FStar_Range.use_range r  in
            let uu____900 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____899 uu____900  in
          if uu____897
          then r
          else
            (let uu____904 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____904)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl = subst' (tl, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____957 ->
          let t0 = t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____963 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____968 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed (t',s') ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1014 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1015 =
                 let uu____1022 =
                   let uu____1023 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1023  in
                 FStar_Syntax_Syntax.mk uu____1022  in
               uu____1015 FStar_Pervasives_Native.None uu____1014
           | uu____1028 ->
               let uu____1029 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1029)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1054  ->
              match uu___5_1054 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1058 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1058
              | f -> f))
  
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1084 =
            let uu____1085 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1085  in
          FStar_Pervasives_Native.Some uu____1084
      | i1 -> i1
  
let (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1132 ->
          let uu___216_1141 = t  in
          let uu____1142 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1147 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1152 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1155 =
            FStar_List.map
              (fun uu____1183  ->
                 match uu____1183 with
                 | (t1,imp) ->
                     let uu____1202 = subst' s t1  in
                     let uu____1203 = subst_imp' s imp  in
                     (uu____1202, uu____1203))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1208 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1142;
            FStar_Syntax_Syntax.effect_name = uu____1147;
            FStar_Syntax_Syntax.result_typ = uu____1152;
            FStar_Syntax_Syntax.effect_args = uu____1155;
            FStar_Syntax_Syntax.flags = uu____1208
          }
  
let (subst_comp' :
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
      | uu____1260 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1281 = subst' s t1  in
               let uu____1282 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1281 uu____1282
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1299 = subst' s t1  in
               let uu____1300 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1299 uu____1300
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1308 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1308)
  
let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n))
      | FStar_Syntax_Syntax.NT uu____1342 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n  -> fun s  -> FStar_List.map (shift n) s 
let shift_subst' :
  'uuuuuu1369 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1369) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'uuuuuu1369)
  =
  fun n  ->
    fun s  ->
      let uu____1400 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n))
         in
      (uu____1400, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1435  ->
      match uu____1435 with
      | (x,imp) ->
          let uu____1454 =
            let uu___269_1455 = x  in
            let uu____1456 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___269_1455.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___269_1455.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1456
            }  in
          let uu____1459 = subst_imp' s imp  in (uu____1454, uu____1459)
  
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
                if i = Prims.int_zero
                then subst_binder' s b
                else
                  (let uu____1565 = shift_subst' i s  in
                   subst_binder' uu____1565 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'uuuuuu1596 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1596) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1596)
  =
  fun s  ->
    fun uu____1614  ->
      match uu____1614 with
      | (t,imp) -> let uu____1621 = subst' s t  in (uu____1621, imp)
  
let subst_args' :
  'uuuuuu1628 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'uuuuuu1628) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1628) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1722 -> (p1, n)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1744 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1806  ->
                      fun uu____1807  ->
                        match (uu____1806, uu____1807) with
                        | ((pats1,n1),(p2,imp)) ->
                            let uu____1903 = aux n1 p2  in
                            (match uu____1903 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n))
               in
            (match uu____1744 with
             | (pats1,n1) ->
                 ((let uu___306_1977 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___306_1977.FStar_Syntax_Syntax.p)
                   }), n1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___311_2003 = x  in
              let uu____2004 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___311_2003.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___311_2003.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2004
              }  in
            ((let uu___314_2009 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___314_2009.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___319_2022 = x  in
              let uu____2023 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___319_2022.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___319_2022.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2023
              }  in
            ((let uu___322_2028 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___322_2028.FStar_Syntax_Syntax.p)
              }), (n + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n s  in
            let x1 =
              let uu___329_2046 = x  in
              let uu____2047 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___329_2046.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___329_2046.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2047
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___333_2053 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___333_2053.FStar_Syntax_Syntax.p)
              }), n)
         in
      aux Prims.int_zero p
  
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
          let uu____2079 =
            let uu___340_2080 = rc  in
            let uu____2081 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___340_2080.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2081;
              FStar_Syntax_Syntax.residual_flags =
                (uu___340_2080.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2079
  
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
               (fun uu____2131  ->
                  match uu____2131 with
                  | (x',uu____2140) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2156 =
          match uu___7_2156 with
          | [] -> []
          | hd_subst::rest ->
              let hd =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2187  ->
                        match uu___6_2187 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2196 = should_retain x  in
                            if uu____2196
                            then
                              let uu____2201 =
                                let uu____2202 =
                                  let uu____2209 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2209)  in
                                FStar_Syntax_Syntax.NT uu____2202  in
                              [uu____2201]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2224 = should_retain x  in
                            if uu____2224
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___367_2232 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___367_2232.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___367_2232.FStar_Syntax_Syntax.sort)
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
                               | uu____2242 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2247 -> []))
                 in
              let uu____2248 = aux rest  in FStar_List.append hd uu____2248
           in
        let uu____2251 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2251 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk t' =
        let uu____2314 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2314  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2317 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2338 ->
               let t1 =
                 let uu____2348 =
                   let uu____2357 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2357  in
                 uu____2348 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2407 -> tag_with_range t s)
      | FStar_Syntax_Syntax.Tm_constant uu____2412 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2417 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2444 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2444 with
           | FStar_Pervasives_Native.None  ->
               let uu____2449 =
                 let uu___400_2452 = t  in
                 let uu____2455 =
                   let uu____2456 =
                     let uu____2469 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2469)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2456  in
                 {
                   FStar_Syntax_Syntax.n = uu____2455;
                   FStar_Syntax_Syntax.pos =
                     (uu___400_2452.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___400_2452.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2449 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2493 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2494 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2495 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2509 = mk (FStar_Syntax_Syntax.Tm_uinst (t', us1))  in
          tag_with_range uu____2509 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2544 =
            let uu____2545 =
              let uu____2562 = subst' s t0  in
              let uu____2565 = subst_args' s args  in
              (uu____2562, uu____2565)  in
            FStar_Syntax_Syntax.Tm_app uu____2545  in
          mk uu____2544
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2666 = subst' s t1  in FStar_Util.Inl uu____2666
            | FStar_Util.Inr c ->
                let uu____2680 = subst_comp' s c  in
                FStar_Util.Inr uu____2680
             in
          let uu____2687 =
            let uu____2688 =
              let uu____2715 = subst' s t0  in
              let uu____2718 =
                let uu____2735 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2735)  in
              (uu____2715, uu____2718, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2688  in
          mk uu____2687
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n = FStar_List.length bs  in
          let s' = shift_subst' n s  in
          let uu____2817 =
            let uu____2818 =
              let uu____2837 = subst_binders' s bs  in
              let uu____2846 = subst' s' body  in
              let uu____2849 = push_subst_lcomp s' lopt  in
              (uu____2837, uu____2846, uu____2849)  in
            FStar_Syntax_Syntax.Tm_abs uu____2818  in
          mk uu____2817
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n = FStar_List.length bs  in
          let uu____2893 =
            let uu____2894 =
              let uu____2909 = subst_binders' s bs  in
              let uu____2918 =
                let uu____2921 = shift_subst' n s  in
                subst_comp' uu____2921 comp  in
              (uu____2909, uu____2918)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2894  in
          mk uu____2893
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___447_2947 = x  in
            let uu____2948 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___447_2947.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___447_2947.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2948
            }  in
          let phi1 =
            let uu____2952 = shift_subst' Prims.int_one s  in
            subst' uu____2952 phi  in
          mk (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3068  ->
                    match uu____3068 with
                    | (pat,wopt,branch) ->
                        let uu____3098 = subst_pat' s pat  in
                        (match uu____3098 with
                         | (pat1,n) ->
                             let s1 = shift_subst' n s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3129 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3129
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n = FStar_List.length lbs  in
          let sn = shift_subst' n s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3198 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3198
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___485_3216 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___485_3216.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___485_3216.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___491_3227 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___491_3227.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___491_3227.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___491_3227.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3279 =
            let uu____3280 =
              let uu____3287 = subst' s t0  in
              let uu____3290 =
                let uu____3291 =
                  let uu____3312 = FStar_List.map (subst' s) bs  in
                  let uu____3321 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3312, uu____3321)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3291  in
              (uu____3287, uu____3290)  in
            FStar_Syntax_Syntax.Tm_meta uu____3280  in
          mk uu____3279
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3403 =
            let uu____3404 =
              let uu____3411 = subst' s t0  in
              let uu____3414 =
                let uu____3415 =
                  let uu____3422 = subst' s t1  in (m, uu____3422)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3415  in
              (uu____3411, uu____3414)  in
            FStar_Syntax_Syntax.Tm_meta uu____3404  in
          mk uu____3403
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3441 =
            let uu____3442 =
              let uu____3449 = subst' s t0  in
              let uu____3452 =
                let uu____3453 =
                  let uu____3462 = subst' s t1  in (m1, m2, uu____3462)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3453  in
              (uu____3449, uu____3452)  in
            FStar_Syntax_Syntax.Tm_meta uu____3442  in
          mk uu____3441
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3477 =
                 let uu____3478 =
                   let uu____3485 = subst' s tm  in (uu____3485, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3478  in
               mk uu____3477
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3499 =
            let uu____3500 = let uu____3507 = subst' s t1  in (uu____3507, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3500  in
          mk uu____3499
  
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = force_uvar t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t',s) ->
        let uu____3551 = push_subst s t'  in compress uu____3551
    | uu____3552 -> t1

and (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3554,uu____3555) ->
        let r = compress_slow t  in r
    | FStar_Syntax_Syntax.Tm_uvar (uu____3579,uu____3580) ->
        let r = compress_slow t  in r
    | uu____3600 -> t

let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3635 =
        let uu____3636 =
          let uu____3637 =
            let uu____3638 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3638  in
          FStar_Syntax_Syntax.SomeUseRange uu____3637  in
        ([], uu____3636)  in
      subst' uu____3635 t
  
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
    let uu____3699 =
      FStar_List.fold_right
        (fun uu____3726  ->
           fun uu____3727  ->
             match (uu____3726, uu____3727) with
             | ((x,uu____3762),(subst1,n)) ->
                 (((FStar_Syntax_Syntax.NM (x, n)) :: subst1),
                   (n + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____3699 FStar_Pervasives_Native.fst
  
let (open_binders' :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___570_3900 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3901 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___570_3900.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___570_3900.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3901
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____3908 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3908  in
          let uu____3914 = aux bs' o1  in
          (match uu____3914 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3975 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3975
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____3997 = open_binders' bs  in
      match uu____3997 with
      | (bs',opening) ->
          let uu____4010 = subst opening t  in (bs', uu____4010, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4026 = open_term' bs t  in
      match uu____4026 with | (b,t1,uu____4039) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4055 = open_binders' bs  in
      match uu____4055 with
      | (bs',opening) ->
          let uu____4066 = subst_comp opening t  in (bs', uu____4066)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4116 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4141 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4212  ->
                    fun uu____4213  ->
                      match (uu____4212, uu____4213) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4327 = open_pat_aux sub1 p2  in
                          (match uu____4327 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4141 with
           | (pats1,sub1) ->
               ((let uu___617_4437 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___617_4437.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___621_4458 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4459 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___621_4458.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___621_4458.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4459
            }  in
          let sub1 =
            let uu____4465 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4465  in
          ((let uu___625_4476 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___625_4476.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___629_4481 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4482 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___629_4481.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___629_4481.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4482
            }  in
          let sub1 =
            let uu____4488 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4488  in
          ((let uu___633_4499 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___633_4499.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___639_4509 = x  in
            let uu____4510 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___639_4509.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___639_4509.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4510
            }  in
          let t01 = subst sub t0  in
          ((let uu___643_4519 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___643_4519.FStar_Syntax_Syntax.p)
            }), sub)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4533  ->
    match uu____4533 with
    | (p,wopt,e) ->
        let uu____4557 = open_pat p  in
        (match uu____4557 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4586 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4586
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4606 = open_branch' br  in
    match uu____4606 with | (br1,uu____4612) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4624 = closing_subst bs  in subst uu____4624 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4638 = closing_subst bs  in subst_comp uu____4638 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl ->
          let x1 =
            let uu___675_4706 = x  in
            let uu____4707 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___675_4706.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___675_4706.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4707
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4714 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4714  in
          let uu____4720 = aux s' tl  in (x1, imp1) :: uu____4720
       in
    aux [] bs
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4784 -> (p1, sub)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4809 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4880  ->
                    fun uu____4881  ->
                      match (uu____4880, uu____4881) with
                      | ((pats1,sub1),(p2,imp)) ->
                          let uu____4995 = aux sub1 p2  in
                          (match uu____4995 with
                           | (p3,sub2) -> (((p3, imp) :: pats1), sub2)))
                 ([], sub))
             in
          (match uu____4809 with
           | (pats1,sub1) ->
               ((let uu___702_5105 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___702_5105.FStar_Syntax_Syntax.p)
                 }), sub1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___706_5126 = x  in
            let uu____5127 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___706_5126.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___706_5126.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5127
            }  in
          let sub1 =
            let uu____5133 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5133  in
          ((let uu___710_5144 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___710_5144.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___714_5149 = x  in
            let uu____5150 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___714_5149.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___714_5149.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5150
            }  in
          let sub1 =
            let uu____5156 = shift_subst Prims.int_one sub  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5156  in
          ((let uu___718_5167 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___718_5167.FStar_Syntax_Syntax.p)
            }), sub1)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___724_5177 = x  in
            let uu____5178 = subst sub x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___724_5177.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___724_5177.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5178
            }  in
          let t01 = subst sub t0  in
          ((let uu___728_5187 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___728_5187.FStar_Syntax_Syntax.p)
            }), sub)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5197  ->
    match uu____5197 with
    | (p,wopt,e) ->
        let uu____5217 = close_pat p  in
        (match uu____5217 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5254 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5254
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us  ->
    let n = (FStar_List.length us) - Prims.int_one  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n = (FStar_List.length us) - Prims.int_one  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____5342 = univ_var_opening us  in
      match uu____5342 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5385 = univ_var_opening us  in
      match uu____5385 with
      | (s,us') -> let uu____5408 = subst_comp s c  in (us', uu____5408)
  
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
      let n = (FStar_List.length us) - Prims.int_one  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5471 =
        let uu____5483 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5483
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5523  ->
                 match uu____5523 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5560 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5560  in
                     ((i + Prims.int_one),
                       ((let uu___780_5568 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___780_5568.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___780_5568.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___780_5568.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___780_5568.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___780_5568.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___780_5568.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5471 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5611 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5641  ->
                             match uu____5641 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + Prims.int_one), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5611 with
                    | (uu____5690,us,u_let_rec_opening) ->
                        let uu___797_5703 = lb  in
                        let uu____5704 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5707 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___797_5703.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5704;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___797_5703.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5707;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___797_5703.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___797_5703.FStar_Syntax_Syntax.lbpos)
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
      let uu____5734 =
        let uu____5742 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5742
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5771  ->
                 match uu____5771 with
                 | (i,out) ->
                     let uu____5794 =
                       let uu____5797 =
                         let uu____5798 =
                           let uu____5804 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5804, i)  in
                         FStar_Syntax_Syntax.NM uu____5798  in
                       uu____5797 :: out  in
                     ((i + Prims.int_one), uu____5794)) lbs
            (Prims.int_zero, [])
         in
      match uu____5734 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5843 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5863  ->
                             match uu____5863 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5843 with
                    | (uu____5894,u_let_rec_closing) ->
                        let uu___819_5902 = lb  in
                        let uu____5903 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5906 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___819_5902.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___819_5902.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5903;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___819_5902.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5906;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___819_5902.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___819_5902.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5922  ->
      match uu____5922 with
      | (us,t) ->
          let n = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5957  ->
                   match uu____5957 with
                   | (x,uu____5966) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5987  ->
      match uu____5987 with
      | (us',t) ->
          let n = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n - i))))
              us
             in
          let uu____6011 = subst s t  in (us', uu____6011)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6030  ->
      match uu____6030 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6044 = subst s1 t  in (us, uu____6044)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6085  ->
              match uu____6085 with
              | (x,uu____6094) -> FStar_Syntax_Syntax.DB ((n - i), x)))
  
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
      let uu____6121 = open_term [b] t  in
      match uu____6121 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6162 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6193 =
        let uu____6198 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6198 t  in
      match uu____6193 with
      | (bs,t1) ->
          let uu____6213 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6213, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6241 = open_term_bvs [bv] t  in
      match uu____6241 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6256 -> failwith "impossible: open_term_bv"
  