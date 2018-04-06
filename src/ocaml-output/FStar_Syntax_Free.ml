open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2)
  =
  let uu____13 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____13)
  
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun fv  ->
    let uu____43 =
      let uu____46 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____46
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____43)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___25_65 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___25_65.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___25_65.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___25_65.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_uv :
  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___26_114 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___26_114.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___26_114.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___26_114.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___27_163 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___27_163.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___27_163.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___27_163.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___28_180 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___28_180.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___28_180.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___28_180.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2)
  =
  fun f1  ->
    fun f2  ->
      let uu____197 =
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
       }, uu____197)
  
let rec (free_univs :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    let uu____247 = FStar_Syntax_Subst.compress_univ u  in
    match uu____247 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____254 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____265 = free_univs x  in union out uu____265)
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
                  fun uu____347  ->
                    match uu____347 with
                    | (x,uu____353) ->
                        let uu____354 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____354) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____356 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____421 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____423 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____424 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____437 = free_univs u  in union out uu____437)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____440) ->
          let uu____461 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____461
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____480 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____480
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____487 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____487
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____524 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____524 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____569 =
            let uu____588 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____611  ->
                   match uu____611 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____661 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____661
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____671 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____671) n1)
                          in
                       let uu____672 = union n11 n2  in union n3 uu____672)
              uu____588
             in
          FStar_All.pipe_right pats uu____569
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____691) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____779 = union u1 u2  in
               let uu____780 = free_names_and_uvars tac use_cache  in
               union uu____779 uu____780)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____799 =
            let uu____804 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____810 =
                     let uu____811 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____812 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____811 uu____812  in
                   union n1 uu____810) uu____804
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____799
      | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static  -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern args ->
               FStar_List.fold_right
                 (fun a  ->
                    fun acc  -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____873,t') ->
               let uu____879 = free_names_and_uvars t' use_cache  in
               union u1 uu____879
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____880,uu____881,t')
               ->
               let uu____887 = free_names_and_uvars t' use_cache  in
               union u1 uu____887
           | FStar_Syntax_Syntax.Meta_labeled uu____888 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____895 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____896 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____902 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____902 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____929 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____929 ->
          let uu____930 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____930)
      | uu____935 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache  in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))

and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 -> Prims.bool -> free_vars_and_fvars)
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1026  ->
                  match uu____1026 with
                  | (x,uu____1034) ->
                      let uu____1039 = free_names_and_uvars x use_cache  in
                      union n1 uu____1039) acc)

and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1053  ->
                  match uu____1053 with
                  | (x,uu____1059) ->
                      let uu____1060 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____1060) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1065 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1065 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1092 = should_invalidate_cache n1 use_cache  in
          if uu____1092
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1118 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____1118))
      | uu____1123 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1149 = free_univs u  in
                let uu____1150 = free_names_and_uvars t use_cache  in
                union uu____1149 uu____1150
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1159 = free_univs u  in
                let uu____1160 = free_names_and_uvars t use_cache  in
                union uu____1159 uu____1160
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1163 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1163 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1175 = free_univs u  in union us1 uu____1175)
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
               (fun uu____1233  ->
                  match uu____1233 with
                  | (u,uu____1241) ->
                      let uu____1246 = FStar_Syntax_Unionfind.find u  in
                      (match uu____1246 with
                       | FStar_Pervasives_Native.Some uu____1249 -> true
                       | uu____1250 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1259 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1259 with
                    | FStar_Pervasives_Native.Some uu____1262 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let compare_uv :
  'Auu____1267 'Auu____1268 .
    (FStar_Syntax_Syntax.uvar,'Auu____1267) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1268) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1293 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1)  in
      let uu____1294 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2)  in
      uu____1293 - uu____1294
  
let (new_uv_set : Prims.unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1297  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1314 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1315 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1314 - uu____1315
  
let (new_universe_uvar_set :
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1320  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1330 =
      let uu____1333 =
        let uu____1334 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1334  in
      uu____1333.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1330 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set)
  =
  fun t  ->
    let uu____1352 =
      let uu____1371 =
        let uu____1372 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1372  in
      uu____1371.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1352 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1406 =
      let uu____1409 =
        let uu____1410 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1410  in
      uu____1409.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1406 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1424 =
      let uu____1427 =
        let uu____1428 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1428  in
      uu____1427.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1424 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____1442 =
      let uu____1445 =
        let uu____1446 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____1446  in
      uu____1445.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1442 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____1460 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____1460
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1474 =
      let uu____1477 =
        let uu____1478 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____1478  in
      uu____1477.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1474 FStar_Syntax_Syntax.order_bv
  