open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
  =
  let uu____13 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____13)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun fv  ->
    let uu____43 =
      let uu____46 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____46 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____43)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___193_65 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___193_65.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___193_65.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___193_65.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let singleton_uv:
  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___194_114 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___194_114.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___194_114.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___194_114.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___195_163 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___195_163.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___195_163.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___195_163.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___196_180 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___196_180.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___196_180.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___196_180.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let union:
  'Auu____188 .
    (FStar_Syntax_Syntax.free_vars,'Auu____188 FStar_Util.set)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.free_vars,'Auu____188 FStar_Util.set)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.free_vars,'Auu____188 FStar_Util.set)
          FStar_Pervasives_Native.tuple2
  =
  fun f1  ->
    fun f2  ->
      let uu____227 =
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
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names)
       }, uu____227)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____277 = FStar_Syntax_Subst.compress_univ u in
    match uu____277 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____284 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____307 = free_univs x in union out uu____307)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
let rec free_names_and_uvs':
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____467  ->
                    match uu____467 with
                    | (x,uu____485) ->
                        let uu____486 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____486) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____494 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____559 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____561 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____592 = free_univs u in union out uu____592)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____601) ->
          let uu____622 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____622
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____647 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____647
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____660 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____660
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____703 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____703 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____748 =
            let uu____773 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____808  ->
                   match uu____808 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____882 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____882
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____910 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____910) n1) in
                       let uu____917 = union n11 n2 in union n3 uu____917)
              uu____773 in
          FStar_All.pipe_right pats uu____748
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____948) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____1054 = union u1 u2 in
               let uu____1061 = free_names_and_uvars tac use_cache in
               union uu____1054 uu____1061)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____1086 =
            let uu____1097 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____1121 =
                     let uu____1128 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____1135 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____1128 uu____1135 in
                   union n1 uu____1121) uu____1097 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1086
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1168 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____1168
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____1208,t')) ->
          let uu____1218 = free_names_and_uvars t1 use_cache in
          let uu____1225 = free_names_and_uvars t' use_cache in
          union uu____1218 uu____1225
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____1233) ->
          free_names_and_uvars t1 use_cache
and free_names_and_uvars:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____1243 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu____1243 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____1303 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____1303 ->
          let uu____1304 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____1304)
      | uu____1309 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))
and free_names_and_uvars_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 -> Prims.bool -> free_vars_and_fvars
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1466  ->
                  match uu____1466 with
                  | (x,uu____1486) ->
                      let uu____1491 = free_names_and_uvars x use_cache in
                      union n1 uu____1491) acc)
and free_names_and_uvars_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
          FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1529  ->
                  match uu____1529 with
                  | (x,uu____1547) ->
                      let uu____1548 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1548) acc)
and free_names_and_uvars_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____1559 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu____1559 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1619 = should_invalidate_cache n1 use_cache in
          if uu____1619
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1678 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1678))
      | uu____1683 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1721 = free_univs u in
                let uu____1728 = free_names_and_uvars t use_cache in
                union uu____1721 uu____1728
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1743 = free_univs u in
                let uu____1750 = free_names_and_uvars t use_cache in
                union uu____1743 uu____1750
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1759 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1759 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1783 = free_univs u in union us1 uu____1783)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun uu____1874  ->
                  match uu____1874 with
                  | (u,uu____1882) ->
                      let uu____1887 = FStar_Syntax_Unionfind.find u in
                      (match uu____1887 with
                       | FStar_Pervasives_Native.Some uu____1890 -> true
                       | uu____1891 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1900 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1900 with
                    | FStar_Pervasives_Native.Some uu____1903 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let compare_uv:
  'Auu____1908 'Auu____1909 .
    (FStar_Syntax_Syntax.uvar,'Auu____1909) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1908) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1934 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1) in
      let uu____1935 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2) in
      uu____1934 - uu____1935
let new_uv_set: Prims.unit -> FStar_Syntax_Syntax.uvars =
  fun uu____1938  -> FStar_Util.new_set compare_uv
let compare_universe_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int
  =
  fun x  ->
    fun y  ->
      let uu____1955 = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu____1956 = FStar_Syntax_Unionfind.univ_uvar_id y in
      uu____1955 - uu____1956
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____1961  -> FStar_Util.new_set compare_universe_uvar
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1969 =
      let uu____1972 =
        let uu____1973 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1973 in
      uu____1972.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1969 FStar_Syntax_Syntax.order_bv
let uvars:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun t  ->
    let uu____1991 =
      let uu____2010 =
        let uu____2011 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____2011 in
      uu____2010.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1991 compare_uv
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____2045 =
      let uu____2048 =
        let uu____2049 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____2049 in
      uu____2048.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu____2045 compare_universe_uvar
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____2063 =
      let uu____2066 =
        let uu____2067 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____2067 in
      uu____2066.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_fifo_set uu____2063 FStar_Syntax_Syntax.order_univ_name
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____2081 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____2081
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____2095 =
      let uu____2098 =
        let uu____2099 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu____2099 in
      uu____2098.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____2095 FStar_Syntax_Syntax.order_bv