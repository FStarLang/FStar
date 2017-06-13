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
    let uu____104 =
      let uu____105 =
        let uu____107 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____107 in
      {
        FStar_Syntax_Syntax.free_names = uu____105;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____111 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____104, uu____111)
let singleton_uv:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____136 =
      let uu____137 =
        let uu____147 = new_uv_set () in FStar_Util.set_add x uu____147 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____137;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____167 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____136, uu____167)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____176 =
      let uu____177 =
        let uu____179 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____179 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____177;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____183 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____176, uu____183)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____192 =
      let uu____193 =
        let uu____195 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____195 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____193
      } in
    let uu____203 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____192, uu____203)
let union f1 f2 =
  let uu____233 =
    let uu____234 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____238 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____258 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____262 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____234;
      FStar_Syntax_Syntax.free_uvars = uu____238;
      FStar_Syntax_Syntax.free_univs = uu____258;
      FStar_Syntax_Syntax.free_univ_names = uu____262
    } in
  let uu____273 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____233, uu____273)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____284 = FStar_Syntax_Subst.compress_univ u in
    match uu____284 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____288 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____301 = free_univs x in union out uu____301)
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
                  fun uu____411  ->
                    match uu____411 with
                    | (x,uu____421) ->
                        let uu____422 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____422) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____427 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____470 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____472 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____491 = free_univs u in union out uu____491)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____497) ->
          let uu____520 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____520
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____536 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____536
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____546 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____546
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____573 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____573 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____605 =
            let uu____622 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____638  ->
                   match uu____638 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____688 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____688
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____702 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____702) n1) in
                       let uu____706 = union n11 n2 in union n3 uu____706)
              uu____622 in
          FStar_All.pipe_right pats uu____605
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____726) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____805 = union u1 u2 in
               let uu____809 = free_names_and_uvars tac use_cache in
               union uu____805 uu____809)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____825 =
            let uu____832 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____844 =
                     let uu____848 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____852 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____848 uu____852 in
                   union n1 uu____844) uu____832 in
          FStar_All.pipe_right (snd lbs) uu____825
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____873 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____873
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____896,t')) ->
          let uu____906 = free_names_and_uvars t1 use_cache in
          let uu____910 = free_names_and_uvars t' use_cache in
          union uu____906 uu____910
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____915) ->
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
      let uu____925 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____925 with
      | Some n1 when
          let uu____934 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____934 ->
          let uu____935 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____935)
      | uu____938 ->
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
                fun uu____977  ->
                  match uu____977 with
                  | (x,uu____989) ->
                      let uu____994 = free_names_and_uvars x use_cache in
                      union n1 uu____994) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____1019  ->
            match uu____1019 with
            | (x,uu____1029) ->
                let uu____1030 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____1030) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1038 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1038 with
      | Some n1 ->
          let uu____1047 = should_invalidate_cache n1 use_cache in
          if uu____1047
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1056 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1056))
      | uu____1059 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1087 = free_univs u in
                let uu____1091 = free_names_and_uvars t use_cache in
                union uu____1087 uu____1091
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1102 = free_univs u in
                let uu____1106 = free_names_and_uvars t use_cache in
                union uu____1102 uu____1106
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1112 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1112 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1124 = free_univs u in union us1 uu____1124)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1135 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1135
            (FStar_Util.for_some
               (fun uu____1184  ->
                  match uu____1184 with
                  | (u,uu____1190) ->
                      let uu____1195 = FStar_Syntax_Unionfind.find u in
                      (match uu____1195 with
                       | Some uu____1197 -> true
                       | uu____1198 -> false))))
           ||
           (let uu____1200 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1200
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1206 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1206 with
                    | Some uu____1208 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1213 =
      let uu____1214 = free_names_and_uvars t true in fst uu____1214 in
    uu____1213.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1225 =
      let uu____1226 = free_names_and_uvars t true in fst uu____1226 in
    uu____1225.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1235 =
      let uu____1236 = free_names_and_uvars t true in fst uu____1236 in
    uu____1235.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1245 =
      let uu____1246 = free_names_and_uvars t true in fst uu____1246 in
    uu____1245.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1256 = free_names_and_uvars t false in snd uu____1256
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1265 =
      let uu____1266 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1266 in
    uu____1265.FStar_Syntax_Syntax.free_names