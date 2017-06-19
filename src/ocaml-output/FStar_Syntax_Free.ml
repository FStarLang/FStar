open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
let new_uv_set:
  Prims.unit ->
    (FStar_Syntax_Syntax.uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun uu____7  ->
    FStar_Util.new_set
      (fun uu____12  ->
         fun uu____13  ->
           match (uu____12, uu____13) with
           | ((x,uu____31),(y,uu____33)) ->
               let uu____50 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____51 = FStar_Syntax_Unionfind.uvar_id y in
               uu____50 - uu____51)
      (fun uu____52  ->
         match uu____52 with
         | (x,uu____58) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____67  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____71 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____72 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____71 - uu____72)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) =
  let uu____78 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____78)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let uu____90 =
      let uu____92 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____92 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____90)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____108 =
      let uu____109 =
        let uu____111 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____111 in
      {
        FStar_Syntax_Syntax.free_names = uu____109;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____115 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____108, uu____115)
let singleton_uv:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____141 =
      let uu____142 =
        let uu____152 = new_uv_set () in FStar_Util.set_add x uu____152 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____142;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____172 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____141, uu____172)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____182 =
      let uu____183 =
        let uu____185 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____185 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____183;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____189 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____182, uu____189)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____199 =
      let uu____200 =
        let uu____202 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____202 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____200
      } in
    let uu____210 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____199, uu____210)
let union f1 f2 =
  let uu____243 =
    let uu____244 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____248 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____268 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____272 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____244;
      FStar_Syntax_Syntax.free_uvars = uu____248;
      FStar_Syntax_Syntax.free_univs = uu____268;
      FStar_Syntax_Syntax.free_univ_names = uu____272
    } in
  let uu____283 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____243, uu____283)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____295 = FStar_Syntax_Subst.compress_univ u in
    match uu____295 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____299 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____312 = free_univs x in union out uu____312)
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
                  fun uu____422  ->
                    match uu____422 with
                    | (x,uu____432) ->
                        let uu____433 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____433) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____438 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____481 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____483 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____502 = free_univs u in union out uu____502)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____508) ->
          let uu____531 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____531
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____547 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____547
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____557 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____557
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____584 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____584 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____616 =
            let uu____633 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____649  ->
                   match uu____649 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____699 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____699
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____713 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____713) n1) in
                       let uu____717 = union n11 n2 in union n3 uu____717)
              uu____633 in
          FStar_All.pipe_right pats uu____616
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____737) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____816 = union u1 u2 in
               let uu____820 = free_names_and_uvars tac use_cache in
               union uu____816 uu____820)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____836 =
            let uu____843 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____855 =
                     let uu____859 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____863 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____859 uu____863 in
                   union n1 uu____855) uu____843 in
          FStar_All.pipe_right (snd lbs) uu____836
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____884 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____884
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____907,t')) ->
          let uu____917 = free_names_and_uvars t1 use_cache in
          let uu____921 = free_names_and_uvars t' use_cache in
          union uu____917 uu____921
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____926) ->
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
      let uu____936 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____936 with
      | Some n1 when
          let uu____945 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____945 ->
          let uu____946 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____946)
      | uu____949 ->
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
                fun uu____988  ->
                  match uu____988 with
                  | (x,uu____1000) ->
                      let uu____1005 = free_names_and_uvars x use_cache in
                      union n1 uu____1005) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____1030  ->
            match uu____1030 with
            | (x,uu____1040) ->
                let uu____1041 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____1041) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1049 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1049 with
      | Some n1 ->
          let uu____1058 = should_invalidate_cache n1 use_cache in
          if uu____1058
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1067 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1067))
      | uu____1070 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1098 = free_univs u in
                let uu____1102 = free_names_and_uvars t use_cache in
                union uu____1098 uu____1102
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1113 = free_univs u in
                let uu____1117 = free_names_and_uvars t use_cache in
                union uu____1113 uu____1117
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1123 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1123 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1135 = free_univs u in union us1 uu____1135)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1146 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1146
            (FStar_Util.for_some
               (fun uu____1195  ->
                  match uu____1195 with
                  | (u,uu____1201) ->
                      let uu____1206 = FStar_Syntax_Unionfind.find u in
                      (match uu____1206 with
                       | Some uu____1208 -> true
                       | uu____1209 -> false))))
           ||
           (let uu____1211 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1211
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1217 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1217 with
                    | Some uu____1219 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1225 =
      let uu____1226 = free_names_and_uvars t true in fst uu____1226 in
    uu____1225.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1238 =
      let uu____1239 = free_names_and_uvars t true in fst uu____1239 in
    uu____1238.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1249 =
      let uu____1250 = free_names_and_uvars t true in fst uu____1250 in
    uu____1249.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1260 =
      let uu____1261 = free_names_and_uvars t true in fst uu____1261 in
    uu____1260.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1272 = free_names_and_uvars t false in snd uu____1272
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1282 =
      let uu____1283 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1283 in
    uu____1282.FStar_Syntax_Syntax.free_names