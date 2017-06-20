open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
let new_uv_set:
  Prims.unit ->
    (FStar_Syntax_Syntax.uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun uu____6  ->
    FStar_Util.new_set
      (fun uu____19  ->
         fun uu____20  ->
           match (uu____19, uu____20) with
           | ((x,uu____38),(y,uu____40)) ->
               let uu____57 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____58 = FStar_Syntax_Unionfind.uvar_id y in
               uu____57 - uu____58)
      (fun uu____62  ->
         match uu____62 with
         | (x,uu____68) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____76  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____84 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____85 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____84 - uu____85)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) =
  let uu____92 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____92)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let uu____103 =
      let uu____105 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____105 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____103)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____116 =
      let uu____117 =
        let uu____119 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____119 in
      {
        FStar_Syntax_Syntax.free_names = uu____117;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____123 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____116, uu____123)
let singleton_uv:
  (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
    FStar_Syntax_Syntax.version)*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____152 =
      let uu____153 =
        let uu____165 = new_uv_set () in FStar_Util.set_add x uu____165 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____153;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____189 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____152, uu____189)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____198 =
      let uu____199 =
        let uu____201 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____201 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____199;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____205 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____198, uu____205)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____214 =
      let uu____215 =
        let uu____217 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____217 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____215
      } in
    let uu____225 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____214, uu____225)
let union f1 f2 =
  let uu____255 =
    let uu____256 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____260 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____284 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____288 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____256;
      FStar_Syntax_Syntax.free_uvars = uu____260;
      FStar_Syntax_Syntax.free_univs = uu____284;
      FStar_Syntax_Syntax.free_univ_names = uu____288
    } in
  let uu____299 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____255, uu____299)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____310 = FStar_Syntax_Subst.compress_univ u in
    match uu____310 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____314 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____330 = free_univs x in union out uu____330)
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
                  fun uu____436  ->
                    match uu____436 with
                    | (x,uu____446) ->
                        let uu____447 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____447) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____452 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____501 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____503 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____525 = free_univs u in union out uu____525)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____531) ->
          let uu____554 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____554
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____570 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____570
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____580 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____580
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____607 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____607 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____637 =
            let uu____653 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____678  ->
                   match uu____678 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____728 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____728
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____745 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____745) n1) in
                       let uu____749 = union n11 n2 in union n3 uu____749)
              uu____653 in
          FStar_All.pipe_right pats uu____637
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____768) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____847 = union u1 u2 in
               let uu____851 = free_names_and_uvars tac use_cache in
               union uu____847 uu____851)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____867 =
            let uu____874 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____889 =
                     let uu____893 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____897 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____893 uu____897 in
                   union n1 uu____889) uu____874 in
          FStar_All.pipe_right (snd lbs) uu____867
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____918 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____918
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____943,t')) ->
          let uu____953 = free_names_and_uvars t1 use_cache in
          let uu____957 = free_names_and_uvars t' use_cache in
          union uu____953 uu____957
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____962) ->
          free_names_and_uvars t1 use_cache
and free_names_and_uvars:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____972 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____972 with
      | Some n1 when
          let uu____981 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____981 ->
          let uu____982 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____982)
      | uu____985 ->
          (FStar_ST.write t1.FStar_Syntax_Syntax.vars None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.write t1.FStar_Syntax_Syntax.vars (Some (fst n1)); n1))
and free_names_and_uvars_args:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1029  ->
                  match uu____1029 with
                  | (x,uu____1041) ->
                      let uu____1046 = free_names_and_uvars x use_cache in
                      union n1 uu____1046) acc)
and free_names_and_uvars_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____1070  ->
                  match uu____1070 with
                  | (x,uu____1080) ->
                      let uu____1081 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1081) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1089 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1089 with
      | Some n1 ->
          let uu____1098 = should_invalidate_cache n1 use_cache in
          if uu____1098
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1107 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1107))
      | uu____1110 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1138 = free_univs u in
                let uu____1142 = free_names_and_uvars t use_cache in
                union uu____1138 uu____1142
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1153 = free_univs u in
                let uu____1157 = free_names_and_uvars t use_cache in
                union uu____1153 uu____1157
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1163 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1163 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1178 = free_univs u in union us1 uu____1178)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1191 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1191
            (FStar_Util.for_some
               (fun uu____1255  ->
                  match uu____1255 with
                  | (u,uu____1261) ->
                      let uu____1266 = FStar_Syntax_Unionfind.find u in
                      (match uu____1266 with
                       | Some uu____1268 -> true
                       | uu____1269 -> false))))
           ||
           (let uu____1272 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1272
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1281 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1281 with
                    | Some uu____1283 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1288 =
      let uu____1289 = free_names_and_uvars t true in fst uu____1289 in
    uu____1288.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1300 =
      let uu____1301 = free_names_and_uvars t true in fst uu____1301 in
    uu____1300.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1310 =
      let uu____1311 = free_names_and_uvars t true in fst uu____1311 in
    uu____1310.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1320 =
      let uu____1321 = free_names_and_uvars t true in fst uu____1321 in
    uu____1320.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1331 = free_names_and_uvars t false in snd uu____1331
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1340 =
      let uu____1341 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1341 in
    uu____1340.FStar_Syntax_Syntax.free_names