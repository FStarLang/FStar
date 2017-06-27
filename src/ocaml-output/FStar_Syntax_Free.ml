open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
let new_uv_set:
  Prims.unit ->
    (FStar_Syntax_Syntax.uvar,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun uu____7  ->
    FStar_Util.new_set
      (fun uu____20  ->
         fun uu____21  ->
           match (uu____20, uu____21) with
           | ((x,uu____39),(y,uu____41)) ->
               let uu____58 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____59 = FStar_Syntax_Unionfind.uvar_id y in
               uu____58 - uu____59)
      (fun uu____63  ->
         match uu____63 with
         | (x,uu____69) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____78  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____86 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____87 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____86 - uu____87)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
  =
  let uu____94 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____94)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun fv  ->
    let uu____106 =
      let uu____108 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____108 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____106)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____120 =
      let uu____121 =
        let uu____123 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____123 in
      {
        FStar_Syntax_Syntax.free_names = uu____121;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____127 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____120, uu____127)
let singleton_uv:
  (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
     FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                      FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____157 =
      let uu____158 =
        let uu____170 = new_uv_set () in FStar_Util.set_add x uu____170 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____158;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____194 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____157, uu____194)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____204 =
      let uu____205 =
        let uu____207 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____207 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____205;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____211 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____204, uu____211)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____221 =
      let uu____222 =
        let uu____224 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____224 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____222
      } in
    let uu____232 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____221, uu____232)
let union f1 f2 =
  let uu____265 =
    let uu____266 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names in
    let uu____270 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____294 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____298 =
      FStar_Util.fifo_set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____266;
      FStar_Syntax_Syntax.free_uvars = uu____270;
      FStar_Syntax_Syntax.free_univs = uu____294;
      FStar_Syntax_Syntax.free_univ_names = uu____298
    } in
  let uu____309 =
    FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
      (FStar_Pervasives_Native.snd f2) in
  (uu____265, uu____309)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____321 = FStar_Syntax_Subst.compress_univ u in
    match uu____321 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____325 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____341 = free_univs x in union out uu____341)
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
                  fun uu____447  ->
                    match uu____447 with
                    | (x,uu____457) ->
                        let uu____458 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____458) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____463 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____506 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____508 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____530 = free_univs u in union out uu____530)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____536) ->
          let uu____549 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____549
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____565 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____565
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____575 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____575
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____602 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____602 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____632 =
            let uu____648 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____673  ->
                   match uu____673 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____723 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____723
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____740 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____740) n1) in
                       let uu____744 = union n11 n2 in union n3 uu____744)
              uu____648 in
          FStar_All.pipe_right pats uu____632
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____763) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____842 = union u1 u2 in
               let uu____846 = free_names_and_uvars tac use_cache in
               union uu____842 uu____846)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____862 =
            let uu____869 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____884 =
                     let uu____888 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____892 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____888 uu____892 in
                   union n1 uu____884) uu____869 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____862
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____913 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____913
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____938,t')) ->
          let uu____948 = free_names_and_uvars t1 use_cache in
          let uu____952 = free_names_and_uvars t' use_cache in
          union uu____948 uu____952
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____957) ->
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
      let uu____967 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____967 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____976 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____976 ->
          let uu____977 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____977)
      | uu____980 ->
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
                fun uu____1024  ->
                  match uu____1024 with
                  | (x,uu____1036) ->
                      let uu____1041 = free_names_and_uvars x use_cache in
                      union n1 uu____1041) acc)
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
                fun uu____1065  ->
                  match uu____1065 with
                  | (x,uu____1075) ->
                      let uu____1076 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1076) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____1084 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1084 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1093 = should_invalidate_cache n1 use_cache in
          if uu____1093
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1102 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1102))
      | uu____1105 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1133 = free_univs u in
                let uu____1137 = free_names_and_uvars t use_cache in
                union uu____1133 uu____1137
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1148 = free_univs u in
                let uu____1152 = free_names_and_uvars t use_cache in
                union uu____1148 uu____1152
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1158 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1158 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1173 = free_univs u in union us1 uu____1173)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1186 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1186
            (FStar_Util.for_some
               (fun uu____1250  ->
                  match uu____1250 with
                  | (u,uu____1256) ->
                      let uu____1261 = FStar_Syntax_Unionfind.find u in
                      (match uu____1261 with
                       | FStar_Pervasives_Native.Some uu____1263 -> true
                       | uu____1264 -> false))))
           ||
           (let uu____1267 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1267
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1276 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1276 with
                    | FStar_Pervasives_Native.Some uu____1278 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1284 =
      let uu____1285 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1285 in
    uu____1284.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
        FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
       FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                        FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun t  ->
    let uu____1297 =
      let uu____1298 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1298 in
    uu____1297.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1308 =
      let uu____1309 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1309 in
    uu____1308.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1319 =
      let uu____1320 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1320 in
    uu____1319.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____1331 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1331
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1341 =
      let uu____1342 = free_names_and_uvars_binders bs no_free_vars true in
      FStar_Pervasives_Native.fst uu____1342 in
    uu____1341.FStar_Syntax_Syntax.free_names