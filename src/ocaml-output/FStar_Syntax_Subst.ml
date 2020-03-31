open Prims
let subst_to_string :
  'Auu____4 . (FStar_Syntax_Syntax.bv * 'Auu____4) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____44  ->
              match uu____44 with
              | (b,uu____51) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____66 'Auu____67 .
    ('Auu____66 -> 'Auu____67 FStar_Pervasives_Native.option) ->
      'Auu____66 Prims.list ->
        ('Auu____66 Prims.list * 'Auu____67) FStar_Pervasives_Native.option
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
  'Auu____142 'Auu____143 'Auu____144 .
    ('Auu____142 -> 'Auu____143 -> 'Auu____144) ->
      'Auu____144 ->
        ('Auu____142 * 'Auu____143) FStar_Pervasives_Native.option ->
          'Auu____144
  =
  fun f  ->
    fun x  ->
      fun uu___0_171  ->
        match uu___0_171 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____207 'Auu____208 'Auu____209 .
    ('Auu____207 -> 'Auu____208 FStar_Pervasives_Native.option) ->
      'Auu____207 Prims.list ->
        ('Auu____207 Prims.list -> 'Auu____208 -> 'Auu____209) ->
          'Auu____209 -> 'Auu____209
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____257 = apply_until_some f s  in
          FStar_All.pipe_right uu____257 (map_some_curry g t)
  
let compose_subst :
  'Auu____283 .
    ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
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
        let uu____472 = FStar_Syntax_Unionfind.find uv  in
        (match uu____472 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____483 =
               let uu____486 =
                 let uu____494 = delay t' s  in force_uvar' uu____494  in
               FStar_Pervasives_Native.fst uu____486  in
             (uu____483, true)
         | uu____504 -> (t, false))
    | uu____511 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____528 = force_uvar' t  in
    match uu____528 with
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
        let uu____572 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____572 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____576 -> u)
    | uu____579 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_601  ->
           match uu___1_601 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____609 =
                 let uu____610 =
                   let uu____611 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____611  in
                 FStar_Syntax_Syntax.bv_to_name uu____610  in
               FStar_Pervasives_Native.Some uu____609
           | uu____612 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_638  ->
           match uu___2_638 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____647 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___91_652 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___91_652.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___91_652.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____647
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____663 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_688  ->
           match uu___3_688 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____696 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_717  ->
           match uu___4_717 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____725 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____753 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____763 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____763
      | FStar_Syntax_Syntax.U_max us ->
          let uu____767 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____767
  
let tag_with_range :
  'Auu____777 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____777 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____803 =
            let uu____805 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____806 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____805 uu____806  in
          if uu____803
          then t
          else
            (let r1 =
               let uu____813 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____813
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____816 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____816
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____818 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____818
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___143_824 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____825 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____825;
                       FStar_Syntax_Syntax.p =
                         (uu___143_824.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___146_827 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___146_827.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___146_827.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___151_829 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___151_829.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____839 .
    FStar_Ident.lident ->
      ('Auu____839 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____859 =
            let uu____861 =
              let uu____862 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____862  in
            let uu____863 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____861 uu____863  in
          if uu____859
          then l
          else
            (let uu____867 =
               let uu____868 = FStar_Ident.range_of_lid l  in
               let uu____869 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____868 uu____869  in
             FStar_Ident.set_lid_range l uu____867)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____886 =
            let uu____888 = FStar_Range.use_range r  in
            let uu____889 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____888 uu____889  in
          if uu____886
          then r
          else
            (let uu____893 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____893)
  
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
      | uu____946 ->
          let t0 = t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____952 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____957 -> tag_with_range t0 s
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
               let uu____1003 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1004 =
                 let uu____1011 =
                   let uu____1012 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1012  in
                 FStar_Syntax_Syntax.mk uu____1011  in
               uu____1004 FStar_Pervasives_Native.None uu____1003
           | uu____1017 ->
               let uu____1018 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1018)
  
let (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1043  ->
              match uu___5_1043 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1047 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1047
              | f -> f))
  
let (subst_imp' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____1073 =
            let uu____1074 =
              let uu____1075 = subst' s t  in
              FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____1075  in
            FStar_Syntax_Syntax.Meta uu____1074  in
          FStar_Pervasives_Native.Some uu____1073
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____1081 =
            let uu____1082 =
              let uu____1083 = subst' s t  in
              FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____1083  in
            FStar_Syntax_Syntax.Meta uu____1082  in
          FStar_Pervasives_Native.Some uu____1081
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
      | uu____1130 ->
          let uu___221_1139 = t  in
          let uu____1140 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1145 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1150 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1153 =
            FStar_List.map
              (fun uu____1181  ->
                 match uu____1181 with
                 | (t1,imp) ->
                     let uu____1200 = subst' s t1  in
                     let uu____1201 = subst_imp' s imp  in
                     (uu____1200, uu____1201))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1206 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1140;
            FStar_Syntax_Syntax.effect_name = uu____1145;
            FStar_Syntax_Syntax.result_typ = uu____1150;
            FStar_Syntax_Syntax.effect_args = uu____1153;
            FStar_Syntax_Syntax.flags = uu____1206
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
      | uu____1258 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1279 = subst' s t1  in
               let uu____1280 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1279 uu____1280
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1297 = subst' s t1  in
               let uu____1298 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1297 uu____1298
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1306 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1306)
  
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
      | FStar_Syntax_Syntax.NT uu____1340 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1367 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1367) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1367)
  =
  fun n1  ->
    fun s  ->
      let uu____1398 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1398, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  FStar_Syntax_Syntax.subst_ts ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1433  ->
      match uu____1433 with
      | (x,imp) ->
          let uu____1452 =
            let uu___274_1453 = x  in
            let uu____1454 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___274_1453.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___274_1453.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1454
            }  in
          let uu____1457 = subst_imp' s imp  in (uu____1452, uu____1457)
  
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
                  (let uu____1563 = shift_subst' i s  in
                   subst_binder' uu____1563 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1594 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1594) ->
        (FStar_Syntax_Syntax.term * 'Auu____1594)
  =
  fun s  ->
    fun uu____1612  ->
      match uu____1612 with
      | (t,imp) -> let uu____1619 = subst' s t  in (uu____1619, imp)
  
let subst_args' :
  'Auu____1626 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1626) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1626) Prims.list
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
        | FStar_Syntax_Syntax.Pat_constant uu____1720 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1742 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1804  ->
                      fun uu____1805  ->
                        match (uu____1804, uu____1805) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1901 = aux n2 p2  in
                            (match uu____1901 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1742 with
             | (pats1,n2) ->
                 ((let uu___311_1975 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___311_1975.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___316_2001 = x  in
              let uu____2002 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___316_2001.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___316_2001.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2002
              }  in
            ((let uu___319_2007 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___319_2007.FStar_Syntax_Syntax.p)
              }), (n1 + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___324_2020 = x  in
              let uu____2021 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___324_2020.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___324_2020.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2021
              }  in
            ((let uu___327_2026 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___327_2026.FStar_Syntax_Syntax.p)
              }), (n1 + Prims.int_one))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___334_2044 = x  in
              let uu____2045 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___334_2044.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___334_2044.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2045
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___338_2051 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___338_2051.FStar_Syntax_Syntax.p)
              }), n1)
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
          let uu____2077 =
            let uu___345_2078 = rc  in
            let uu____2079 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___345_2078.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2079;
              FStar_Syntax_Syntax.residual_flags =
                (uu___345_2078.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2077
  
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
               (fun uu____2129  ->
                  match uu____2129 with
                  | (x',uu____2138) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2154 =
          match uu___7_2154 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2185  ->
                        match uu___6_2185 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2194 = should_retain x  in
                            if uu____2194
                            then
                              let uu____2199 =
                                let uu____2200 =
                                  let uu____2207 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2207)  in
                                FStar_Syntax_Syntax.NT uu____2200  in
                              [uu____2199]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2222 = should_retain x  in
                            if uu____2222
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___372_2230 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___372_2230.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___372_2230.FStar_Syntax_Syntax.sort)
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
                               | uu____2240 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2245 -> []))
                 in
              let uu____2246 = aux rest  in FStar_List.append hd1 uu____2246
           in
        let uu____2249 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2249 with
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
        let uu____2312 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2312  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2315 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2336 ->
               let t1 =
                 let uu____2346 =
                   let uu____2355 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2355  in
                 uu____2346 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2405 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2406 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2411 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2438 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2438 with
           | FStar_Pervasives_Native.None  ->
               let uu____2443 =
                 let uu___405_2446 = t  in
                 let uu____2449 =
                   let uu____2450 =
                     let uu____2463 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2463)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2450  in
                 {
                   FStar_Syntax_Syntax.n = uu____2449;
                   FStar_Syntax_Syntax.pos =
                     (uu___405_2446.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___405_2446.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2443 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2487 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2488 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2489 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2503 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2503 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2536 =
            let uu____2537 =
              let uu____2554 = subst' s t0  in
              let uu____2557 = subst_args' s args  in
              (uu____2554, uu____2557)  in
            FStar_Syntax_Syntax.Tm_app uu____2537  in
          mk1 uu____2536
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2658 = subst' s t1  in FStar_Util.Inl uu____2658
            | FStar_Util.Inr c ->
                let uu____2672 = subst_comp' s c  in
                FStar_Util.Inr uu____2672
             in
          let uu____2679 =
            let uu____2680 =
              let uu____2707 = subst' s t0  in
              let uu____2710 =
                let uu____2727 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2727)  in
              (uu____2707, uu____2710, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2680  in
          mk1 uu____2679
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2809 =
            let uu____2810 =
              let uu____2829 = subst_binders' s bs  in
              let uu____2838 = subst' s' body  in
              let uu____2841 = push_subst_lcomp s' lopt  in
              (uu____2829, uu____2838, uu____2841)  in
            FStar_Syntax_Syntax.Tm_abs uu____2810  in
          mk1 uu____2809
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2885 =
            let uu____2886 =
              let uu____2901 = subst_binders' s bs  in
              let uu____2910 =
                let uu____2913 = shift_subst' n1 s  in
                subst_comp' uu____2913 comp  in
              (uu____2901, uu____2910)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2886  in
          mk1 uu____2885
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___452_2939 = x  in
            let uu____2940 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___452_2939.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___452_2939.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2940
            }  in
          let phi1 =
            let uu____2944 = shift_subst' Prims.int_one s  in
            subst' uu____2944 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3060  ->
                    match uu____3060 with
                    | (pat,wopt,branch) ->
                        let uu____3090 = subst_pat' s pat  in
                        (match uu____3090 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3121 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3121
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
                      let uu____3190 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3190
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___490_3208 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_3208.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_3208.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let lbattrs =
                      FStar_List.map (subst' s)
                        lb.FStar_Syntax_Syntax.lbattrs
                       in
                    let uu___496_3219 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___496_3219.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___496_3219.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs = lbattrs;
                      FStar_Syntax_Syntax.lbpos =
                        (uu___496_3219.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_pattern (bs,ps)) ->
          let uu____3271 =
            let uu____3272 =
              let uu____3279 = subst' s t0  in
              let uu____3282 =
                let uu____3283 =
                  let uu____3304 = FStar_List.map (subst' s) bs  in
                  let uu____3313 =
                    FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                     in
                  (uu____3304, uu____3313)  in
                FStar_Syntax_Syntax.Meta_pattern uu____3283  in
              (uu____3279, uu____3282)  in
            FStar_Syntax_Syntax.Tm_meta uu____3272  in
          mk1 uu____3271
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3395 =
            let uu____3396 =
              let uu____3403 = subst' s t0  in
              let uu____3406 =
                let uu____3407 =
                  let uu____3414 = subst' s t1  in (m, uu____3414)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3407  in
              (uu____3403, uu____3406)  in
            FStar_Syntax_Syntax.Tm_meta uu____3396  in
          mk1 uu____3395
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3433 =
            let uu____3434 =
              let uu____3441 = subst' s t0  in
              let uu____3444 =
                let uu____3445 =
                  let uu____3454 = subst' s t1  in (m1, m2, uu____3454)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3445  in
              (uu____3441, uu____3444)  in
            FStar_Syntax_Syntax.Tm_meta uu____3434  in
          mk1 uu____3433
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3469 =
                 let uu____3470 =
                   let uu____3477 = subst' s tm  in (uu____3477, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3470  in
               mk1 uu____3469
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3491 =
            let uu____3492 = let uu____3499 = subst' s t1  in (uu____3499, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3492  in
          mk1 uu____3491
  
let rec (compress_slow :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let t1 = force_uvar t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (t',s) -> push_subst s t'
    | uu____3539 -> t1
  
let (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (uu____3546,uu____3547) ->
        compress_slow t
    | FStar_Syntax_Syntax.Tm_uvar (uu____3568,uu____3569) -> compress_slow t
    | uu____3586 -> t
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3621 =
        let uu____3622 =
          let uu____3623 =
            let uu____3624 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3624  in
          FStar_Syntax_Syntax.SomeUseRange uu____3623  in
        ([], uu____3622)  in
      subst' uu____3621 t
  
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
    let uu____3685 =
      FStar_List.fold_right
        (fun uu____3712  ->
           fun uu____3713  ->
             match (uu____3712, uu____3713) with
             | ((x,uu____3748),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + Prims.int_one))) bs ([], Prims.int_zero)
       in
    FStar_All.pipe_right uu____3685 FStar_Pervasives_Native.fst
  
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
            let uu___574_3886 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3887 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___574_3886.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___574_3886.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3887
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____3894 = shift_subst Prims.int_one o  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____3894  in
          let uu____3900 = aux bs' o1  in
          (match uu____3900 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3961 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3961
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____3983 = open_binders' bs  in
      match uu____3983 with
      | (bs',opening) ->
          let uu____3996 = subst opening t  in (bs', uu____3996, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4012 = open_term' bs t  in
      match uu____4012 with | (b,t1,uu____4025) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4041 = open_binders' bs  in
      match uu____4041 with
      | (bs',opening) ->
          let uu____4052 = subst_comp opening t  in (bs', uu____4052)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4102 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4127 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4198  ->
                    fun uu____4199  ->
                      match (uu____4198, uu____4199) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4313 = open_pat_aux sub2 p2  in
                          (match uu____4313 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4127 with
           | (pats1,sub2) ->
               ((let uu___621_4423 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___621_4423.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___625_4444 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4445 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___625_4444.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___625_4444.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4445
            }  in
          let sub2 =
            let uu____4451 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4451  in
          ((let uu___629_4462 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___629_4462.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___633_4467 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4468 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___633_4467.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___633_4467.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4468
            }  in
          let sub2 =
            let uu____4474 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.DB (Prims.int_zero, x')) :: uu____4474  in
          ((let uu___637_4485 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___637_4485.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___643_4495 = x  in
            let uu____4496 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___643_4495.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___643_4495.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4496
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___647_4505 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___647_4505.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4519  ->
    match uu____4519 with
    | (p,wopt,e) ->
        let uu____4543 = open_pat p  in
        (match uu____4543 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4572 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4572
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4592 = open_branch' br  in
    match uu____4592 with | (br1,uu____4598) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4610 = closing_subst bs  in subst uu____4610 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4624 = closing_subst bs  in subst_comp uu____4624 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___679_4692 = x  in
            let uu____4693 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_4692.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_4692.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4693
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____4700 = shift_subst Prims.int_one s  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____4700  in
          let uu____4706 = aux s' tl1  in (x1, imp1) :: uu____4706
       in
    aux [] bs
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4770 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4795 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4866  ->
                    fun uu____4867  ->
                      match (uu____4866, uu____4867) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4981 = aux sub2 p2  in
                          (match uu____4981 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4795 with
           | (pats1,sub2) ->
               ((let uu___706_5091 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___706_5091.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___710_5112 = x  in
            let uu____5113 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___710_5112.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___710_5112.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5113
            }  in
          let sub2 =
            let uu____5119 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5119  in
          ((let uu___714_5130 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___714_5130.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___718_5135 = x  in
            let uu____5136 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___718_5135.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___718_5135.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5136
            }  in
          let sub2 =
            let uu____5142 = shift_subst Prims.int_one sub1  in
            (FStar_Syntax_Syntax.NM (x1, Prims.int_zero)) :: uu____5142  in
          ((let uu___722_5153 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___722_5153.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___728_5163 = x  in
            let uu____5164 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___728_5163.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___728_5163.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5164
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___732_5173 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___732_5173.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5183  ->
    match uu____5183 with
    | (p,wopt,e) ->
        let uu____5203 = close_pat p  in
        (match uu____5203 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5240 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5240
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us  ->
    let n1 = (FStar_List.length us) - Prims.int_one  in
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
    let n1 = (FStar_List.length us) - Prims.int_one  in
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
      let uu____5328 = univ_var_opening us  in
      match uu____5328 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5371 = univ_var_opening us  in
      match uu____5371 with
      | (s,us') -> let uu____5394 = subst_comp s c  in (us', uu____5394)
  
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
      let n1 = (FStar_List.length us) - Prims.int_one  in
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
      let uu____5457 =
        let uu____5469 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5469
        then (Prims.int_zero, lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5509  ->
                 match uu____5509 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5546 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5546  in
                     ((i + Prims.int_one),
                       ((let uu___784_5554 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___784_5554.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___784_5554.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___784_5554.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___784_5554.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___784_5554.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___784_5554.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs (Prims.int_zero, [], [])
         in
      match uu____5457 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5597 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5627  ->
                             match uu____5627 with
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
                    match uu____5597 with
                    | (uu____5676,us,u_let_rec_opening) ->
                        let uu___801_5689 = lb  in
                        let uu____5690 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5693 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___801_5689.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5690;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___801_5689.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5693;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___801_5689.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___801_5689.FStar_Syntax_Syntax.lbpos)
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
      let uu____5720 =
        let uu____5728 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5728
        then (Prims.int_zero, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5757  ->
                 match uu____5757 with
                 | (i,out) ->
                     let uu____5780 =
                       let uu____5783 =
                         let uu____5784 =
                           let uu____5790 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5790, i)  in
                         FStar_Syntax_Syntax.NM uu____5784  in
                       uu____5783 :: out  in
                     ((i + Prims.int_one), uu____5780)) lbs
            (Prims.int_zero, [])
         in
      match uu____5720 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5829 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5849  ->
                             match uu____5849 with
                             | (i,out) ->
                                 ((i + Prims.int_one),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5829 with
                    | (uu____5880,u_let_rec_closing) ->
                        let uu___823_5888 = lb  in
                        let uu____5889 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5892 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___823_5888.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___823_5888.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5889;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___823_5888.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5892;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___823_5888.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___823_5888.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5908  ->
      match uu____5908 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - Prims.int_one  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5943  ->
                   match uu____5943 with
                   | (x,uu____5952) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5973  ->
      match uu____5973 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - Prims.int_one  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5997 = subst s t  in (us', uu____5997)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6016  ->
      match uu____6016 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6030 = subst s1 t  in (us, uu____6030)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - Prims.int_one  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6071  ->
              match uu____6071 with
              | (x,uu____6080) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
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
      let uu____6107 = open_term [b] t  in
      match uu____6107 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6148 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6179 =
        let uu____6184 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6184 t  in
      match uu____6179 with
      | (bs,t1) ->
          let uu____6199 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6199, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6227 = open_term_bvs [bv] t  in
      match uu____6227 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6242 -> failwith "impossible: open_term_bv"
  