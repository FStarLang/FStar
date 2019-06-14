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
    let uu____29 =
      let uu____32 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____32 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____29)
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___2_54 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___2_54.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___2_54.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___2_54.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___5_74 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___5_74.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___5_74.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___5_74.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___8_94 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___8_94.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___8_94.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___8_94.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___11_114 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___11_114.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___11_114.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___11_114.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1 ->
    fun f2 ->
      let uu____136 =
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
       }, uu____136)
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u ->
    let uu____167 = FStar_Syntax_Subst.compress_univ u in
    match uu____167 with
    | FStar_Syntax_Syntax.U_zero -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____168 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out ->
             fun x -> let uu____180 = free_univs x in union out uu____180)
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
               (fun n1 ->
                  fun uu____321 ->
                    match uu____321 with
                    | (x, uu____329) ->
                        let uu____334 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____334) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____336 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv, uu____362) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____380 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____382 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____383 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out ->
               fun u -> let uu____396 = free_univs u in union out uu____396)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____399) ->
          let uu____424 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____424
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____447 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____447
      | FStar_Syntax_Syntax.Tm_refine (bv, t1) ->
          let uu____454 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____454
      | FStar_Syntax_Syntax.Tm_app (t1, args) ->
          let uu____495 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____495 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
          let uu____540 =
            let uu____559 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1 ->
                 fun uu____582 ->
                   match uu____582 with
                   | (p, wopt, t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____620 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____620
                           (FStar_List.fold_left
                              (fun n3 ->
                                 fun x ->
                                   let uu____630 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____630) n1) in
                       let uu____631 = union n11 n2 in union n3 uu____631)
              uu____559 in
          FStar_All.pipe_right pats uu____540
      | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____648) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____736 = union u1 u2 in
               let uu____737 = free_names_and_uvars tac use_cache in
               union uu____736 uu____737)
      | FStar_Syntax_Syntax.Tm_let (lbs, t1) ->
          let uu____758 =
            let uu____765 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1 ->
                 fun lb ->
                   let uu____771 =
                     let uu____772 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____773 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____772 uu____773 in
                   union n1 uu____771) uu____765 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____758
      | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let u1 = free_names_and_uvars t1 use_cache in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____792, args) ->
               FStar_List.fold_right
                 (fun a ->
                    fun acc -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____862, t') ->
               let uu____868 = free_names_and_uvars t' use_cache in
               union u1 uu____868
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____869, uu____870, t')
               ->
               let uu____876 = free_names_and_uvars t' use_cache in
               union u1 uu____876
           | FStar_Syntax_Syntax.Meta_labeled uu____877 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____886 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____887 -> u1)
and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t ->
    fun use_cache ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____894 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu____894 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____921 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____921 ->
          let uu____923 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____923)
      | uu____928 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))
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
             (fun n1 ->
                fun uu____1032 ->
                  match uu____1032 with
                  | (x, uu____1042) ->
                      let uu____1051 = free_names_and_uvars x use_cache in
                      union n1 uu____1051) acc)
and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs ->
    fun acc ->
      fun use_cache ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1 ->
                fun uu____1076 ->
                  match uu____1076 with
                  | (x, uu____1084) ->
                      let uu____1089 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1089) acc)
and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c ->
    fun use_cache ->
      let uu____1095 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu____1095 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1122 = should_invalidate_cache n1 use_cache in
          if uu____1122
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1151 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1151))
      | uu____1156 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1194 = free_univs u in
                let uu____1195 = free_names_and_uvars t use_cache in
                union uu____1194 uu____1195
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1204 = free_univs u in
                let uu____1205 = free_names_and_uvars t use_cache in
                union uu____1204 uu____1205
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1214 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1214 use_cache in
                FStar_List.fold_left
                  (fun us1 ->
                     fun u ->
                       let uu____1226 = free_univs u in union us1 uu____1226)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1 ->
    fun use_cache ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun u ->
                  let uu____1263 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                  match uu____1263 with
                  | FStar_Pervasives_Native.Some uu____1267 -> true
                  | uu____1269 -> false)))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u ->
                    let uu____1280 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1280 with
                    | FStar_Pervasives_Native.Some uu____1284 -> true
                    | FStar_Pervasives_Native.None -> false))))
let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1 ->
    fun uv2 ->
      let uu____1299 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head in
      let uu____1301 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head in
      uu____1299 - uu____1301
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1308 -> FStar_Util.new_set compare_uv
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x ->
    fun y ->
      let uu____1321 = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu____1323 = FStar_Syntax_Unionfind.univ_uvar_id y in
      uu____1321 - uu____1323
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1332 -> FStar_Util.new_set compare_universe_uvar
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t ->
    let uu____1346 =
      let uu____1349 =
        let uu____1350 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1350 in
      uu____1349.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1346 FStar_Syntax_Syntax.order_bv
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t ->
    let uu____1368 =
      let uu____1371 =
        let uu____1372 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1372 in
      uu____1371.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1368 compare_uv
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t ->
    let uu____1390 =
      let uu____1393 =
        let uu____1394 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1394 in
      uu____1393.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu____1390 compare_universe_uvar
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t ->
    let uu____1412 =
      let uu____1415 =
        let uu____1416 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1416 in
      uu____1415.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1412 FStar_Syntax_Syntax.order_univ_name
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c ->
    let uu____1434 =
      let uu____1437 =
        let uu____1438 = free_names_and_uvars_comp c true in
        FStar_Pervasives_Native.fst uu____1438 in
      uu____1437.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1434 FStar_Syntax_Syntax.order_univ_name
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t ->
    let uu____1456 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1456
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs ->
    let uu____1474 =
      let uu____1477 =
        let uu____1478 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu____1478 in
      uu____1477.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1474 FStar_Syntax_Syntax.order_bv