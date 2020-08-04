open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu____12 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____12)
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun fv ->
    let uu____28 =
      let uu____31 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____31 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____28)
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___2_52 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___2_52.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___2_52.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___2_52.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___5_71 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___5_71.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___5_71.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___5_71.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___8_90 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___8_90.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___8_90.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___8_90.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___11_109 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___11_109.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___11_109.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___11_109.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1 ->
    fun f2 ->
      let uu____130 =
        FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
          (FStar_Pervasives_Native.snd f2) in
      ({
         FStar_Syntax_Syntax.free_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names);
         FStar_Syntax_Syntax.free_uvars =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars);
         FStar_Syntax_Syntax.free_univs =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs);
         FStar_Syntax_Syntax.free_univ_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)
       }, uu____130)
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u ->
    let uu____160 = FStar_Syntax_Subst.compress_univ u in
    match uu____160 with
    | FStar_Syntax_Syntax.U_zero -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____161 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out ->
             fun x -> let uu____172 = free_univs x in union out uu____172)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm ->
    fun use_cache ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n ->
                  fun uu____294 ->
                    match uu____294 with
                    | (x, uu____302) ->
                        let uu____307 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n uu____307) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____309 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv, uu____326) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____344 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____346 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____347 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out ->
               fun u -> let uu____360 = free_univs u in union out uu____360)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____363) ->
          let uu____388 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____388
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____411 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____411
      | FStar_Syntax_Syntax.Tm_refine (bv, t1) ->
          let uu____418 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____418
      | FStar_Syntax_Syntax.Tm_app (t1, args) ->
          let uu____459 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____459 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
          let uu____504 =
            let uu____523 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n ->
                 fun uu____546 ->
                   match uu____546 with
                   | (p, wopt, t2) ->
                       let n1 =
                         match wopt with
                         | FStar_Pervasives_Native.None -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____584 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____584
                           (FStar_List.fold_left
                              (fun n3 ->
                                 fun x ->
                                   let uu____594 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____594) n) in
                       let uu____595 = union n1 n2 in union n3 uu____595)
              uu____523 in
          FStar_All.pipe_right pats uu____504
      | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____612) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____700 = union u1 u2 in
               let uu____701 = free_names_and_uvars tac use_cache in
               union uu____700 uu____701)
      | FStar_Syntax_Syntax.Tm_let (lbs, t1) ->
          let uu____720 =
            let uu____727 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n ->
                 fun lb ->
                   let uu____733 =
                     let uu____734 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____735 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____734 uu____735 in
                   union n uu____733) uu____727 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____720
      | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let u1 = free_names_and_uvars t1 use_cache in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____753, args) ->
               FStar_List.fold_right
                 (fun a ->
                    fun acc -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____823, t') ->
               let uu____829 = free_names_and_uvars t' use_cache in
               union u1 uu____829
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____830, uu____831, t')
               ->
               let uu____837 = free_names_and_uvars t' use_cache in
               union u1 uu____837
           | FStar_Syntax_Syntax.Meta_labeled uu____838 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____845 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____846 -> u1)
and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t ->
    fun use_cache ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____852 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu____852 with
      | FStar_Pervasives_Native.Some n when
          let uu____866 = should_invalidate_cache n use_cache in
          Prims.op_Negation uu____866 ->
          let uu____867 = FStar_Syntax_Syntax.new_fv_set () in (n, uu____867)
      | uu____872 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n = free_names_and_uvs' t1 use_cache in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n));
            n))
and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun args ->
    fun acc ->
      fun use_cache ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n ->
                fun uu____949 ->
                  match uu____949 with
                  | (x, uu____959) ->
                      let uu____968 = free_names_and_uvars x use_cache in
                      union n uu____968) acc)
and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c ->
    fun use_cache ->
      let uu____973 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu____973 with
      | FStar_Pervasives_Native.Some n ->
          let uu____987 = should_invalidate_cache n use_cache in
          if uu____987
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1000 = FStar_Syntax_Syntax.new_fv_set () in
             (n, uu____1000))
      | uu____1005 ->
          let n =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1043 = free_univs u in
                let uu____1044 = free_names_and_uvars t use_cache in
                union uu____1043 uu____1044
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1053 = free_univs u in
                let uu____1054 = free_names_and_uvars t use_cache in
                union uu____1053 uu____1054
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1063 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1063 use_cache in
                FStar_List.fold_left
                  (fun us1 ->
                     fun u ->
                       let uu____1075 = free_univs u in union us1 uu____1075)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n));
           n)
and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n ->
    fun use_cache ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun u ->
                  let uu____1097 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                  match uu____1097 with
                  | FStar_Pervasives_Native.Some uu____1100 -> true
                  | uu____1101 -> false)))
           ||
           (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u ->
                    let uu____1110 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1110 with
                    | FStar_Pervasives_Native.Some uu____1113 -> true
                    | FStar_Pervasives_Native.None -> false))))
let (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs ->
    fun acc ->
      fun use_cache ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n ->
                fun uu____1149 ->
                  match uu____1149 with
                  | (x, uu____1157) ->
                      let uu____1162 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n uu____1162) acc)
let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1 ->
    fun uv2 ->
      let uu____1173 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head in
      let uu____1174 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head in
      uu____1173 - uu____1174
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1179 -> FStar_Util.new_set compare_uv
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x ->
    fun y ->
      let uu____1190 = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu____1191 = FStar_Syntax_Unionfind.univ_uvar_id y in
      uu____1190 - uu____1191
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1198 -> FStar_Util.new_set compare_universe_uvar
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t ->
    let uu____1210 =
      let uu____1213 =
        let uu____1214 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1214 in
      uu____1213.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1210 FStar_Syntax_Syntax.order_bv
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t ->
    let uu____1230 =
      let uu____1233 =
        let uu____1234 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1234 in
      uu____1233.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1230 compare_uv
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t ->
    let uu____1250 =
      let uu____1253 =
        let uu____1254 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1254 in
      uu____1253.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu____1250 compare_universe_uvar
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t ->
    let uu____1270 =
      let uu____1273 =
        let uu____1274 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1274 in
      uu____1273.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1270 FStar_Syntax_Syntax.order_univ_name
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c ->
    let uu____1290 =
      let uu____1293 =
        let uu____1294 = free_names_and_uvars_comp c true in
        FStar_Pervasives_Native.fst uu____1294 in
      uu____1293.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1290 FStar_Syntax_Syntax.order_univ_name
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t ->
    let uu____1310 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1310
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs ->
    let uu____1326 =
      let uu____1329 =
        let uu____1330 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu____1330 in
      uu____1329.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1326 FStar_Syntax_Syntax.order_bv
let (uvars_uncached :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t ->
    let uu____1346 =
      let uu____1349 =
        let uu____1350 = free_names_and_uvars t false in
        FStar_Pervasives_Native.fst uu____1350 in
      uu____1349.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1346 compare_uv