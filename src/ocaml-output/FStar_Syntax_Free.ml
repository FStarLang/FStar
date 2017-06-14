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
      (fun uu____11  ->
         fun uu____12  ->
           match (uu____11, uu____12) with
           | ((x,uu____30),(y,uu____32)) ->
               let uu____49 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____50 = FStar_Syntax_Unionfind.uvar_id y in
               uu____49 - uu____50)
      (fun uu____51  ->
         match uu____51 with
         | (x,uu____57) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____65  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____69 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____70 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____69 - uu____70)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) =
  let uu____76 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____76)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let uu____87 =
      let uu____89 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____89 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____87)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____100 =
      let uu____101 =
        let uu____103 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____103 in
      {
        FStar_Syntax_Syntax.free_names = uu____101;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____107 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____100, uu____107)
let singleton_uv:
  (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
    FStar_Syntax_Syntax.version)*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____136 =
      let uu____137 =
        let uu____149 = new_uv_set () in FStar_Util.set_add x uu____149 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____137;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____173 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____136, uu____173)
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
    let uu____198 =
      let uu____199 =
        let uu____201 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____201 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____199
      } in
    let uu____209 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____198, uu____209)
let union f1 f2 =
  let uu____239 =
    let uu____240 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____244 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____268 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____272 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____240;
      FStar_Syntax_Syntax.free_uvars = uu____244;
      FStar_Syntax_Syntax.free_univs = uu____268;
      FStar_Syntax_Syntax.free_univ_names = uu____272
    } in
  let uu____283 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____239, uu____283)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____294 = FStar_Syntax_Subst.compress_univ u in
    match uu____294 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____298 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____311 = free_univs x in union out uu____311)
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
                  fun uu____423  ->
                    match uu____423 with
                    | (x,uu____433) ->
                        let uu____434 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____434) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____439 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____488 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____490 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____509 = free_univs u in union out uu____509)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____515) ->
          let uu____538 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____538
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____554 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____554
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____564 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____564
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____591 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____591 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____621 =
            let uu____637 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____653  ->
                   match uu____653 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____703 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____703
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____717 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____717) n1) in
                       let uu____721 = union n11 n2 in union n3 uu____721)
              uu____637 in
          FStar_All.pipe_right pats uu____621
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____740) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____819 = union u1 u2 in
               let uu____823 = free_names_and_uvars tac use_cache in
               union uu____819 uu____823)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____839 =
            let uu____846 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____858 =
                     let uu____862 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____866 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____862 uu____866 in
                   union n1 uu____858) uu____846 in
          FStar_All.pipe_right (snd lbs) uu____839
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____887 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____887
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____910,t')) ->
          let uu____920 = free_names_and_uvars t1 use_cache in
          let uu____924 = free_names_and_uvars t' use_cache in
          union uu____920 uu____924
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____929) ->
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
      let uu____939 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____939 with
      | Some n1 when
          let uu____948 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____948 ->
          let uu____949 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____949)
      | uu____952 ->
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
                fun uu____991  ->
                  match uu____991 with
                  | (x,uu____1003) ->
                      let uu____1008 = free_names_and_uvars x use_cache in
                      union n1 uu____1008) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____1033  ->
            match uu____1033 with
            | (x,uu____1043) ->
                let uu____1044 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____1044) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1052 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1052 with
      | Some n1 ->
          let uu____1061 = should_invalidate_cache n1 use_cache in
          if uu____1061
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1070 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1070))
      | uu____1073 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1101 = free_univs u in
                let uu____1105 = free_names_and_uvars t use_cache in
                union uu____1101 uu____1105
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1116 = free_univs u in
                let uu____1120 = free_names_and_uvars t use_cache in
                union uu____1116 uu____1120
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1126 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1126 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1138 = free_univs u in union us1 uu____1138)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1149 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1149
            (FStar_Util.for_some
               (fun uu____1208  ->
                  match uu____1208 with
                  | (u,uu____1214) ->
                      let uu____1219 = FStar_Syntax_Unionfind.find u in
                      (match uu____1219 with
                       | Some uu____1221 -> true
                       | uu____1222 -> false))))
           ||
           (let uu____1224 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1224
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1230 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1230 with
                    | Some uu____1232 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1237 =
      let uu____1238 = free_names_and_uvars t true in fst uu____1238 in
    uu____1237.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1249 =
      let uu____1250 = free_names_and_uvars t true in fst uu____1250 in
    uu____1249.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1259 =
      let uu____1260 = free_names_and_uvars t true in fst uu____1260 in
    uu____1259.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1269 =
      let uu____1270 = free_names_and_uvars t true in fst uu____1270 in
    uu____1269.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1280 = free_names_and_uvars t false in snd uu____1280
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1289 =
      let uu____1290 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1290 in
    uu____1289.FStar_Syntax_Syntax.free_names