open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
  =
  let uu____13 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
     FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____13)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun fv  ->
    let uu____27 =
      let uu____30 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____30 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
       FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____27)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____48 =
      let uu____49 =
        let uu____52 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____52 in
      {
        FStar_Syntax_Syntax.free_names = uu____49;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____55 = FStar_Syntax_Syntax.new_fv_set () in (uu____48, uu____55)
let singleton_uv:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
     FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
     FStar_Unionfind.uvar,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                            FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____101 =
      let uu____102 =
        let uu____121 = FStar_Syntax_Syntax.new_uv_set () in
        FStar_Util.set_add x uu____121 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____102;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____156 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____101, uu____156)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____170 =
      let uu____171 =
        let uu____174 = FStar_Syntax_Syntax.new_universe_uvar_set () in
        FStar_Util.set_add x uu____174 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____171;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____177 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____170, uu____177)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____191 =
      let uu____192 =
        let uu____195 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____195 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____192
      } in
    let uu____202 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____191, uu____202)
let union f1 f2 =
  let uu____249 =
    let uu____250 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names in
    let uu____257 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____296 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____303 =
      FStar_Util.fifo_set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____250;
      FStar_Syntax_Syntax.free_uvars = uu____257;
      FStar_Syntax_Syntax.free_univs = uu____296;
      FStar_Syntax_Syntax.free_univ_names = uu____303
    } in
  let uu____312 =
    FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
      (FStar_Pervasives_Native.snd f2) in
  (uu____249, uu____312)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____330 = FStar_Syntax_Subst.compress_univ u in
    match uu____330 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____337 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____357 = free_univs x in union out uu____357)
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
                  fun uu____528  ->
                    match uu____528 with
                    | (x,uu____546) ->
                        let uu____547 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____547) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____555 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____634 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____636 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____668 = free_univs u in union out uu____668)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____677) ->
          let uu____722 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____722
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____751 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____751
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____768 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____768
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____819 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____819 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____880 =
            let uu____911 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____941  ->
                   match uu____941 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____1033 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____1033
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____1058 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____1058) n1) in
                       let uu____1065 = union n11 n2 in union n3 uu____1065)
              uu____911 in
          FStar_All.pipe_right pats uu____880
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____1102) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____1254 = union u1 u2 in
               let uu____1261 = free_names_and_uvars tac use_cache in
               union uu____1254 uu____1261)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____1290 =
            let uu____1301 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____1322 =
                     let uu____1329 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____1336 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____1329 uu____1336 in
                   union n1 uu____1322) uu____1301 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1290
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1375 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____1375
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____1417,t')) ->
          let uu____1435 = free_names_and_uvars t1 use_cache in
          let uu____1442 = free_names_and_uvars t' use_cache in
          union uu____1435 uu____1442
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____1450) ->
          free_names_and_uvars t1 use_cache
and free_names_and_uvars:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____1466 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____1466 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____1478 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____1478 ->
          let uu____1479 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____1479)
      | uu____1484 ->
          (FStar_ST.write t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.write t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))
and free_names_and_uvars_args:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
     FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
          FStar_Pervasives_Native.tuple2
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1546  ->
                  match uu____1546 with
                  | (x,uu____1568) ->
                      let uu____1577 = free_names_and_uvars x use_cache in
                      union n1 uu____1577) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____1622  ->
            match uu____1622 with
            | (x,uu____1640) ->
                let uu____1641 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____1641) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____1654 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1654 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1666 = should_invalidate_cache n1 use_cache in
          if uu____1666
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1677 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1677))
      | uu____1682 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1732 = free_univs u in
                let uu____1739 = free_names_and_uvars t use_cache in
                union uu____1732 uu____1739
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1758 = free_univs u in
                let uu____1765 = free_names_and_uvars t use_cache in
                union uu____1758 uu____1765
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1774 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1774 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1795 = free_univs u in union us1 uu____1795)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1809 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1809
            (FStar_Util.for_some
               (fun uu____1914  ->
                  match uu____1914 with
                  | (u,uu____1932) ->
                      let uu____1957 = FStar_Unionfind.find u in
                      (match uu____1957 with
                       | FStar_Syntax_Syntax.Fixed uu____1970 -> true
                       | uu____1979 -> false))))
           ||
           (let uu____1986 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1986
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____2004 = FStar_Unionfind.find u in
                    match uu____2004 with
                    | FStar_Pervasives_Native.Some uu____2009 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____2015 =
      let uu____2016 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2016 in
    uu____2015.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
       FStar_Unionfind.uvar,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                              FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun t  ->
    let uu____2034 =
      let uu____2035 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2035 in
    uu____2034.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____2049 =
      let uu____2050 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2050 in
    uu____2049.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____2064 =
      let uu____2065 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2065 in
    uu____2064.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____2079 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____2079
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____2093 =
      let uu____2094 = free_names_and_uvars_binders bs no_free_vars true in
      FStar_Pervasives_Native.fst uu____2094 in
    uu____2093.FStar_Syntax_Syntax.free_names