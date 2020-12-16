open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu___ = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu___)
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun fv ->
    let uu___ =
      let uu___1 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu___1 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu___)
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___ = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_uv :
  FStar_Syntax_Syntax.ctx_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___ = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___ = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x ->
    ((let uu___ = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun f1 ->
    fun f2 ->
      let uu___ =
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
       }, uu___)
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u ->
    let uu___ = FStar_Syntax_Subst.compress_univ u in
    match uu___ with
    | FStar_Syntax_Syntax.U_zero -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu___1 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out -> fun x -> let uu___1 = free_univs x in union out uu___1)
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
                  fun uu___ ->
                    match uu___ with
                    | (x, uu___1) ->
                        let uu___2 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n uu___2) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv, uu___) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu___ -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu___ -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out -> fun u -> let uu___ = free_univs u in union out uu___)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu___) ->
          let uu___1 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu___1
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu___ = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu___
      | FStar_Syntax_Syntax.Tm_refine (bv, t1) ->
          let uu___ = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu___
      | FStar_Syntax_Syntax.Tm_app (t1, args) ->
          let uu___ = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu___ use_cache
      | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
          let uu___ =
            let uu___1 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n ->
                 fun uu___2 ->
                   match uu___2 with
                   | (p, wopt, t2) ->
                       let n1 =
                         match wopt with
                         | FStar_Pervasives_Native.None -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu___3 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu___3
                           (FStar_List.fold_left
                              (fun n4 ->
                                 fun x ->
                                   let uu___4 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n4 uu___4) n) in
                       let uu___3 = union n1 n2 in union n3 uu___3) uu___1 in
          FStar_All.pipe_right pats uu___
      | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu___) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu___1 = union u1 u2 in
               let uu___2 = free_names_and_uvars tac use_cache in
               union uu___1 uu___2)
      | FStar_Syntax_Syntax.Tm_let (lbs, t1) ->
          let uu___ =
            let uu___1 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n ->
                 fun lb ->
                   let uu___2 =
                     let uu___3 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu___4 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu___3 uu___4 in
                   union n uu___2) uu___1 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu___
      | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let u1 = free_names_and_uvars t1 use_cache in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu___, args) ->
               FStar_List.fold_right
                 (fun a ->
                    fun acc -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu___, t') ->
               let uu___1 = free_names_and_uvars t' use_cache in
               union u1 uu___1
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu___, uu___1, t') ->
               let uu___2 = free_names_and_uvars t' use_cache in
               union u1 uu___2
           | FStar_Syntax_Syntax.Meta_labeled uu___ -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu___ -> u1
           | FStar_Syntax_Syntax.Meta_named uu___ -> u1)
and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t ->
    fun use_cache ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu___ = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu___ with
      | FStar_Pervasives_Native.Some n when
          let uu___1 = should_invalidate_cache n use_cache in
          Prims.op_Negation uu___1 ->
          let uu___1 = FStar_Syntax_Syntax.new_fv_set () in (n, uu___1)
      | uu___1 ->
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
                fun uu___ ->
                  match uu___ with
                  | (x, uu___1) ->
                      let uu___2 = free_names_and_uvars x use_cache in
                      union n uu___2) acc)
and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c ->
    fun use_cache ->
      let uu___ = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu___ with
      | FStar_Pervasives_Native.Some n ->
          let uu___1 = should_invalidate_cache n use_cache in
          if uu___1
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu___3 = FStar_Syntax_Syntax.new_fv_set () in (n, uu___3))
      | uu___1 ->
          let n =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u)
                ->
                let uu___2 = free_univs u in
                let uu___3 = free_names_and_uvars t use_cache in
                union uu___2 uu___3
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u)
                ->
                let uu___2 = free_univs u in
                let uu___3 = free_names_and_uvars t use_cache in
                union uu___2 uu___3
            | FStar_Syntax_Syntax.Comp ct ->
                let decreases_vars =
                  let uu___2 =
                    FStar_List.tryFind
                      (fun uu___3 ->
                         match uu___3 with
                         | FStar_Syntax_Syntax.DECREASES uu___4 -> true
                         | uu___4 -> false) ct.FStar_Syntax_Syntax.flags in
                  match uu___2 with
                  | FStar_Pervasives_Native.None -> no_free_vars
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.DECREASES d) ->
                      free_names_and_uvars d use_cache
                  | FStar_Pervasives_Native.Some uu___3 ->
                      failwith "impossible" in
                let us =
                  let uu___2 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  union uu___2 decreases_vars in
                let us1 =
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args us use_cache in
                FStar_List.fold_left
                  (fun us2 ->
                     fun u -> let uu___2 = free_univs u in union us2 uu___2)
                  us1 ct.FStar_Syntax_Syntax.comp_univs in
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
                  let uu___ =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head in
                  match uu___ with
                  | FStar_Pervasives_Native.Some uu___1 -> true
                  | uu___1 -> false)))
           ||
           (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u ->
                    let uu___ = FStar_Syntax_Unionfind.univ_find u in
                    match uu___ with
                    | FStar_Pervasives_Native.Some uu___1 -> true
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
                fun uu___ ->
                  match uu___ with
                  | (x, uu___1) ->
                      let uu___2 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n uu___2) acc)
let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1 ->
    fun uv2 ->
      let uu___ =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head in
      let uu___1 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head in
      uu___ - uu___1
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu___ -> FStar_Util.new_set compare_uv
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x ->
    fun y ->
      let uu___ = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu___1 = FStar_Syntax_Unionfind.univ_uvar_id y in uu___ - uu___1
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu___ -> FStar_Util.new_set compare_universe_uvar
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu___ FStar_Syntax_Syntax.order_bv
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu___ compare_uv
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu___ compare_universe_uvar
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu___ FStar_Syntax_Syntax.order_univ_name
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars_comp c true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu___ FStar_Syntax_Syntax.order_univ_name
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t ->
    let uu___ = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu___
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu___ FStar_Syntax_Syntax.order_bv
let (uvars_uncached :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = free_names_and_uvars t false in
        FStar_Pervasives_Native.fst uu___2 in
      uu___1.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu___ compare_uv