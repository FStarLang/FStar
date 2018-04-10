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
    let uu____45 =
      let uu____48 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____48
       in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____45)
  
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___25_69 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___25_69.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___25_69.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___25_69.FStar_Syntax_Syntax.free_univ_names)
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
    ((let uu___26_120 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___26_120.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___26_120.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___26_120.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___27_171 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___27_171.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___27_171.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___27_171.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___28_190 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___28_190.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___28_190.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___28_190.FStar_Syntax_Syntax.free_univs);
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
      let uu____211 =
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
       }, uu____211)
  
let rec (free_univs :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    let uu____263 = FStar_Syntax_Subst.compress_univ u  in
    match uu____263 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____270 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____281 = free_univs x  in union out uu____281)
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
                  fun uu____393  ->
                    match uu____393 with
                    | (x,uu____399) ->
                        let uu____400 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____400) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____402 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____467 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____469 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____470 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____483 = free_univs u  in union out uu____483)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____486) ->
          let uu____507 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____507
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____526 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____526
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____533 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____533
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____570 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____570 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____615 =
            let uu____635 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____658  ->
                   match uu____658 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____708 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____708
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____718 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____718) n1)
                          in
                       let uu____719 = union n11 n2  in union n3 uu____719)
              uu____635
             in
          FStar_All.pipe_right pats uu____615
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____738) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____826 = union u1 u2  in
               let uu____827 = free_names_and_uvars tac use_cache  in
               union uu____826 uu____827)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____846 =
            let uu____852 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____858 =
                     let uu____859 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____860 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____859 uu____860  in
                   union n1 uu____858) uu____852
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____846
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
           | FStar_Syntax_Syntax.Meta_monadic (uu____921,t') ->
               let uu____927 = free_names_and_uvars t' use_cache  in
               union u1 uu____927
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____928,uu____929,t')
               ->
               let uu____935 = free_names_and_uvars t' use_cache  in
               union u1 uu____935
           | FStar_Syntax_Syntax.Meta_labeled uu____936 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____943 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____944 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____950 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____950 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____981 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____981 ->
          let uu____982 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____982)
      | uu____987 ->
          let uu____990 =
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              FStar_Pervasives_Native.None
             in
          let n1 = free_names_and_uvs' t1 use_cache  in
          let uu____1019 =
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1))
             in
          n1

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
                fun uu____1086  ->
                  match uu____1086 with
                  | (x,uu____1094) ->
                      let uu____1099 = free_names_and_uvars x use_cache  in
                      union n1 uu____1099) acc)

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
                fun uu____1113  ->
                  match uu____1113 with
                  | (x,uu____1119) ->
                      let uu____1120 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____1120) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1125 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1125 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1156 = should_invalidate_cache n1 use_cache  in
          if uu____1156
          then
            let uu____1157 =
              FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
                FStar_Pervasives_Native.None
               in
            free_names_and_uvars_comp c use_cache
          else
            (let uu____1186 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____1186))
      | uu____1191 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1217 = free_univs u  in
                let uu____1218 = free_names_and_uvars t use_cache  in
                union uu____1217 uu____1218
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1227 = free_univs u  in
                let uu____1228 = free_names_and_uvars t use_cache  in
                union uu____1227 uu____1228
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1231 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1231 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1243 = free_univs u  in union us1 uu____1243)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1244 =
            FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1))
             in
          n1

and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun uu____1305  ->
                  match uu____1305 with
                  | (u,uu____1313) ->
                      let uu____1318 = FStar_Syntax_Unionfind.find u  in
                      (match uu____1318 with
                       | FStar_Pervasives_Native.Some uu____1321 -> true
                       | uu____1322 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1331 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1331 with
                    | FStar_Pervasives_Native.Some uu____1334 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let compare_uv :
  'Auu____1343 'Auu____1344 .
    (FStar_Syntax_Syntax.uvar,'Auu____1343) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1344) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1371 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1)  in
      let uu____1372 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2)  in
      uu____1371 - uu____1372
  
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1377  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1398 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1399 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1398 - uu____1399
  
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1406  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1418 =
      let uu____1421 =
        let uu____1422 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1422  in
      uu____1421.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1418 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set)
  =
  fun t  ->
    let uu____1442 =
      let uu____1461 =
        let uu____1462 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1462  in
      uu____1461.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1442 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1498 =
      let uu____1501 =
        let uu____1502 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1502  in
      uu____1501.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1498 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1518 =
      let uu____1521 =
        let uu____1522 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1522  in
      uu____1521.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1518 FStar_Syntax_Syntax.order_univ_name
  
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c  ->
    let uu____1538 =
      let uu____1541 =
        let uu____1542 = free_names_and_uvars_comp c true  in
        FStar_Pervasives_Native.fst uu____1542  in
      uu____1541.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1538 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____1558 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____1558
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1574 =
      let uu____1577 =
        let uu____1578 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____1578  in
      uu____1577.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1574 FStar_Syntax_Syntax.order_bv
  