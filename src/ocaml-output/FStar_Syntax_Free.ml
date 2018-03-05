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
    ((let uu___23_65 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___23_65.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___23_65.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___23_65.FStar_Syntax_Syntax.free_univ_names)
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
    ((let uu___24_114 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___24_114.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___24_114.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___24_114.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___25_163 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___25_163.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___25_163.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___25_163.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    ((let uu___26_180 = FStar_Pervasives_Native.fst no_free_vars  in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___26_180.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___26_180.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___26_180.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
  
let union :
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
       }, uu____227)
  
let rec (free_univs :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    let uu____277 = FStar_Syntax_Subst.compress_univ u  in
    match uu____277 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____284 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____307 = free_univs x  in union out uu____307)
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
                  fun uu____467  ->
                    match uu____467 with
                    | (x,uu____485) ->
                        let uu____486 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____486) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____494 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____559 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____561 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____562 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____593 = free_univs u  in union out uu____593)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____602) ->
          let uu____623 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____623
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____648 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____648
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____661 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____661
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____704 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____704 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____749 =
            let uu____774 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____809  ->
                   match uu____809 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____883 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____883
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____911 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____911) n1)
                          in
                       let uu____918 = union n11 n2  in union n3 uu____918)
              uu____774
             in
          FStar_All.pipe_right pats uu____749
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____949) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____1055 = union u1 u2  in
               let uu____1062 = free_names_and_uvars tac use_cache  in
               union uu____1055 uu____1062)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____1087 =
            let uu____1098 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____1122 =
                     let uu____1129 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____1136 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____1129 uu____1136  in
                   union n1 uu____1122) uu____1098
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1087
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1169 = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____1169
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____1209,t')) ->
          let uu____1219 = free_names_and_uvars t1 use_cache  in
          let uu____1226 = free_names_and_uvars t' use_cache  in
          union uu____1219 uu____1226
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____1234) ->
          free_names_and_uvars t1 use_cache

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____1244 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____1244 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____1277 = should_invalidate_cache n1 use_cache  in
          Prims.op_Negation uu____1277 ->
          let uu____1278 = FStar_Syntax_Syntax.new_fv_set ()  in
          (n1, uu____1278)
      | uu____1283 ->
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
                fun uu____1386  ->
                  match uu____1386 with
                  | (x,uu____1406) ->
                      let uu____1411 = free_names_and_uvars x use_cache  in
                      union n1 uu____1411) acc)

and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
          FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1449  ->
                  match uu____1449 with
                  | (x,uu____1467) ->
                      let uu____1468 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____1468) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1479 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1479 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1512 = should_invalidate_cache n1 use_cache  in
          if uu____1512
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1544 = FStar_Syntax_Syntax.new_fv_set ()  in
             (n1, uu____1544))
      | uu____1549 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1587 = free_univs u  in
                let uu____1594 = free_names_and_uvars t use_cache  in
                union uu____1587 uu____1594
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1609 = free_univs u  in
                let uu____1616 = free_names_and_uvars t use_cache  in
                union uu____1609 uu____1616
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1625 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1625 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1649 = free_univs u  in union us1 uu____1649)
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
               (fun uu____1713  ->
                  match uu____1713 with
                  | (u,uu____1721) ->
                      let uu____1726 = FStar_Syntax_Unionfind.find u  in
                      (match uu____1726 with
                       | FStar_Pervasives_Native.Some uu____1729 -> true
                       | uu____1730 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1739 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1739 with
                    | FStar_Pervasives_Native.Some uu____1742 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let compare_uv :
  'Auu____1747 'Auu____1748 .
    (FStar_Syntax_Syntax.uvar,'Auu____1748) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1747) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1773 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1)  in
      let uu____1774 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2)  in
      uu____1773 - uu____1774
  
let (new_uv_set : Prims.unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1777  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1794 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1795 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1794 - uu____1795
  
let (new_universe_uvar_set :
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1800  -> FStar_Util.new_set compare_universe_uvar 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1808 =
      let uu____1811 =
        let uu____1812 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1812  in
      uu____1811.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1808 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set)
  =
  fun t  ->
    let uu____1830 =
      let uu____1849 =
        let uu____1850 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1850  in
      uu____1849.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1830 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1884 =
      let uu____1887 =
        let uu____1888 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1888  in
      uu____1887.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1884 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1902 =
      let uu____1905 =
        let uu____1906 = free_names_and_uvars t true  in
        FStar_Pervasives_Native.fst uu____1906  in
      uu____1905.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1902 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  ->
    let uu____1920 = free_names_and_uvars t false  in
    FStar_Pervasives_Native.snd uu____1920
  
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1934 =
      let uu____1937 =
        let uu____1938 = free_names_and_uvars_binders bs no_free_vars true
           in
        FStar_Pervasives_Native.fst uu____1938  in
      uu____1937.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1934 FStar_Syntax_Syntax.order_bv
  