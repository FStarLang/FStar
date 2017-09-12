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
    let uu____44 =
      let uu____47 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____47 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____44)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___147_67 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___147_67.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___147_67.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___147_67.FStar_Syntax_Syntax.free_univ_names)
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
    ((let uu___148_117 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___148_117.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___148_117.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___148_117.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___149_167 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___149_167.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___149_167.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___149_167.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    ((let uu___150_185 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___150_185.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___150_185.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___150_185.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let union:
  'Auu____196 .
    (FStar_Syntax_Syntax.free_vars,'Auu____196 FStar_Util.set)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.free_vars,'Auu____196 FStar_Util.set)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.free_vars,'Auu____196 FStar_Util.set)
          FStar_Pervasives_Native.tuple2
  =
  fun f1  ->
    fun f2  ->
      let uu____235 =
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
       }, uu____235)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____286 = FStar_Syntax_Subst.compress_univ u in
    match uu____286 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____293 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____316 = free_univs x in union out uu____316)
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
                  fun uu____476  ->
                    match uu____476 with
                    | (x,uu____494) ->
                        let uu____495 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____495) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____503 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____568 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____570 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____601 = free_univs u in union out uu____601)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____610) ->
          let uu____631 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____631
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____656 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____656
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____669 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____669
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____712 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____712 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____757 =
            let uu____782 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____817  ->
                   match uu____817 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____891 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____891
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____919 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____919) n1) in
                       let uu____926 = union n11 n2 in union n3 uu____926)
              uu____782 in
          FStar_All.pipe_right pats uu____757
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____957) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____1063 = union u1 u2 in
               let uu____1070 = free_names_and_uvars tac use_cache in
               union uu____1063 uu____1070)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____1095 =
            let uu____1106 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____1130 =
                     let uu____1137 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____1144 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____1137 uu____1144 in
                   union n1 uu____1130) uu____1106 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1095
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1177 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____1177
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____1217,t')) ->
          let uu____1227 = free_names_and_uvars t1 use_cache in
          let uu____1234 = free_names_and_uvars t' use_cache in
          union uu____1227 uu____1234
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____1242) ->
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
      let uu____1252 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu____1252 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____1280 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____1280 ->
          let uu____1281 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____1281)
      | uu____1286 ->
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
                fun uu____1379  ->
                  match uu____1379 with
                  | (x,uu____1399) ->
                      let uu____1404 = free_names_and_uvars x use_cache in
                      union n1 uu____1404) acc)
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
                fun uu____1442  ->
                  match uu____1442 with
                  | (x,uu____1460) ->
                      let uu____1461 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1461) acc)
and free_names_and_uvars_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____1472 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu____1472 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1500 = should_invalidate_cache n1 use_cache in
          if uu____1500
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1527 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1527))
      | uu____1532 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1570 = free_univs u in
                let uu____1577 = free_names_and_uvars t use_cache in
                union uu____1570 uu____1577
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1592 = free_univs u in
                let uu____1599 = free_names_and_uvars t use_cache in
                union uu____1592 uu____1599
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1608 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1608 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1632 = free_univs u in union us1 uu____1632)
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
               (fun uu____1691  ->
                  match uu____1691 with
                  | (u,uu____1699) ->
                      let uu____1704 = FStar_Syntax_Unionfind.find u in
                      (match uu____1704 with
                       | FStar_Pervasives_Native.Some uu____1707 -> true
                       | uu____1708 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1717 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1717 with
                    | FStar_Pervasives_Native.Some uu____1720 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let compare_uv:
  'Auu____1729 'Auu____1730 .
    (FStar_Syntax_Syntax.uvar,'Auu____1730) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1729) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1755 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1) in
      let uu____1756 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2) in
      uu____1755 - uu____1756
let new_uv_set: Prims.unit -> FStar_Syntax_Syntax.uvars =
  fun uu____1760  -> FStar_Util.new_set compare_uv
let compare_universe_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int
  =
  fun x  ->
    fun y  ->
      let uu____1779 = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu____1780 = FStar_Syntax_Unionfind.univ_uvar_id y in
      uu____1779 - uu____1780
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____1786  -> FStar_Util.new_set compare_universe_uvar
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1795 =
      let uu____1798 =
        let uu____1799 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1799 in
      uu____1798.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1795 FStar_Syntax_Syntax.order_bv
let uvars:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun t  ->
    let uu____1818 =
      let uu____1837 =
        let uu____1838 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1838 in
      uu____1837.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1818 compare_uv
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1873 =
      let uu____1876 =
        let uu____1877 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1877 in
      uu____1876.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu____1873 compare_universe_uvar
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1892 =
      let uu____1895 =
        let uu____1896 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1896 in
      uu____1895.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_fifo_set uu____1892 FStar_Syntax_Syntax.order_univ_name
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____1911 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1911
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1926 =
      let uu____1929 =
        let uu____1930 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu____1930 in
      uu____1929.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1926 FStar_Syntax_Syntax.order_bv