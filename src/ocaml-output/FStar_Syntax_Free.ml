open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)) =
  let uu____12 = FStar_Syntax_Syntax.new_fv_set ()  in
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
  fun fv  ->
    let uu____29 =
      let uu____32 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____32
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____29)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set))
  =
  fun x  ->
    ((let uu___2_54 = FStar_Pervasives_Native.fst no_free_vars  in
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
  fun x  ->
    ((let uu___5_74 = FStar_Pervasives_Native.fst no_free_vars  in
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
  fun x  ->
    ((let uu___8_94 = FStar_Pervasives_Native.fst no_free_vars  in
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
  fun x  ->
    ((let uu___11_114 = FStar_Pervasives_Native.fst no_free_vars  in
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
  fun f1  ->
    fun f2  ->
      let uu____136 =
        FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
          (FStar_Pervasives_Native.snd f2)
         in
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
  fun u  ->
    let uu____167 = FStar_Syntax_Subst.compress_univ u  in
    match uu____167 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____168 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____180 = free_univs x  in union out uu____180)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
  
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____308  ->
                    match uu____308 with
                    | (x,uu____316) ->
                        let uu____321 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____321) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____323 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (uv,uu____341) -> singleton_uv uv
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____359 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____361 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____362 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____375 = free_univs u  in union out uu____375)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____378) ->
          let uu____403 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____403
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____426 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____426
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____433 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____433
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____474 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____474 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____519 =
            let uu____538 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____561  ->
                   match uu____561 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____599 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____599
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____609 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____609) n1)
                          in
                       let uu____610 = union n11 n2  in union n3 uu____610)
              uu____538
             in
          FStar_All.pipe_right pats uu____519
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____627) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____715 = union u1 u2  in
               let uu____716 = free_names_and_uvars tac use_cache  in
               union uu____715 uu____716)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____737 =
            let uu____744 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____750 =
                     let uu____751 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____752 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____751 uu____752  in
                   union n1 uu____750) uu____744
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____737
      | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static  -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____771,args) ->
               FStar_List.fold_right
                 (fun a  ->
                    fun acc  -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____841,t') ->
               let uu____847 = free_names_and_uvars t' use_cache  in
               union u1 uu____847
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____848,uu____849,t')
               ->
               let uu____855 = free_names_and_uvars t' use_cache  in
               union u1 uu____855
           | FStar_Syntax_Syntax.Meta_labeled uu____856 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____865 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____866 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____873 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____873 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____900 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____900 ->
          let uu____902 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____902)
      | uu____907 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache  in
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
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1011  ->
                  match uu____1011 with
                  | (x,uu____1021) ->
                      let uu____1030 = free_names_and_uvars x use_cache  in
                      union n1 uu____1030) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1036 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1036 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1063 = should_invalidate_cache n1 use_cache  in
          if uu____1063
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1092 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____1092))
      | uu____1097 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1135 = free_univs u  in
                let uu____1136 = free_names_and_uvars t use_cache  in
                union uu____1135 uu____1136
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1145 = free_univs u  in
                let uu____1146 = free_names_and_uvars t use_cache  in
                union uu____1145 uu____1146
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1155 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1155 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1167 = free_univs u  in union us1 uu____1167)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)

and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun u  ->
                  let uu____1204 =
                    FStar_Syntax_Unionfind.find
                      u.FStar_Syntax_Syntax.ctx_uvar_head
                     in
                  match uu____1204 with
                  | FStar_Pervasives_Native.Some uu____1208 -> true
                  | uu____1210 -> false)))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1221 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1221 with
                    | FStar_Pervasives_Native.Some uu____1225 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1266  ->
                  match uu____1266 with
                  | (x,uu____1274) ->
                      let uu____1279 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____1279) acc)
  
let (compare_uv :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.int)
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1292 =
        FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head
         in
      let uu____1294 =
        FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head
         in
      uu____1292 - uu____1294
  
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1301  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1314 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1316 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1314 - uu____1316
  
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1325  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1339 =
      let uu____1342 =
        let uu____1343 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1343  in
      uu____1342.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1339 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t  ->
    let uu____1361 =
      let uu____1364 =
        let uu____1365 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1365  in
      uu____1364.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1361 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1383 =
      let uu____1386 =
        let uu____1387 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1387  in
      uu____1386.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1383 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1405 =
      let uu____1408 =
        let uu____1409 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1409  in
      uu____1408.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1405 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____1427 =
      let uu____1430 =
        let uu____1431 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____1431  in
      uu____1430.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1427 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____1449 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____1449
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1467 =
      let uu____1470 =
        let uu____1471 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____1471  in
      uu____1470.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1467 FStar_Syntax_Syntax.order_bv
  
let (uvars_uncached :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun t  ->
    let uu____1489 =
      let uu____1492 =
        let uu____1493 = free_names_and_uvars t false  in
        FStar_Pervasives_Native.fst uu____1493  in
      uu____1492.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1489 compare_uv
  