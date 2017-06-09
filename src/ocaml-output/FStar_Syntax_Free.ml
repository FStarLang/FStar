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
  (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
    FStar_Syntax_Syntax.version)*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____140 =
      let uu____141 =
        let uu____153 = new_uv_set () in FStar_Util.set_add x uu____153 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____141;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____177 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____140, uu____177)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____186 =
      let uu____187 =
        let uu____189 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____189 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____187;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____193 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____186, uu____193)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____202 =
      let uu____203 =
        let uu____205 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____205 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____203
      } in
    let uu____213 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____202, uu____213)
let union f1 f2 =
  let uu____243 =
    let uu____244 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____248 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____272 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____276 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____244;
      FStar_Syntax_Syntax.free_uvars = uu____248;
      FStar_Syntax_Syntax.free_univs = uu____272;
      FStar_Syntax_Syntax.free_univ_names = uu____276
    } in
  let uu____287 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____243, uu____287)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____298 = FStar_Syntax_Subst.compress_univ u in
    match uu____298 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____302 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____315 = free_univs x in union out uu____315)
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
                  fun uu____427  ->
                    match uu____427 with
                    | (x,uu____437) ->
                        let uu____438 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____438) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____443 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____492 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____494 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____513 = free_univs u in union out uu____513)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____519) ->
          let uu____542 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____542
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____558 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____558
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____568 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____568
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____595 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____595 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____627 =
            let uu____644 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____660  ->
                   match uu____660 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____710 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____710
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____724 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____724) n1) in
                       let uu____728 = union n11 n2 in union n3 uu____728)
              uu____644 in
          FStar_All.pipe_right pats uu____627
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____748) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____827 = union u1 u2 in
               let uu____831 = free_names_and_uvars tac use_cache in
               union uu____827 uu____831)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____847 =
            let uu____854 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____866 =
                     let uu____870 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____874 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____870 uu____874 in
                   union n1 uu____866) uu____854 in
          FStar_All.pipe_right (snd lbs) uu____847
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____895 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____895
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____918,t')) ->
          let uu____928 = free_names_and_uvars t1 use_cache in
          let uu____932 = free_names_and_uvars t' use_cache in
          union uu____928 uu____932
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____937) ->
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
      let uu____947 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____947 with
      | Some n1 when
          let uu____956 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____956 ->
          let uu____957 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____957)
      | uu____960 ->
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
                fun uu____999  ->
                  match uu____999 with
                  | (x,uu____1011) ->
                      let uu____1016 = free_names_and_uvars x use_cache in
                      union n1 uu____1016) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____1041  ->
            match uu____1041 with
            | (x,uu____1051) ->
                let uu____1052 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____1052) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1060 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1060 with
      | Some n1 ->
          let uu____1069 = should_invalidate_cache n1 use_cache in
          if uu____1069
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1078 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1078))
      | uu____1081 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1109 = free_univs u in
                let uu____1113 = free_names_and_uvars t use_cache in
                union uu____1109 uu____1113
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1124 = free_univs u in
                let uu____1128 = free_names_and_uvars t use_cache in
                union uu____1124 uu____1128
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1134 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1134 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1146 = free_univs u in union us1 uu____1146)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1157 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1157
            (FStar_Util.for_some
               (fun uu____1216  ->
                  match uu____1216 with
                  | (u,uu____1222) ->
                      let uu____1227 = FStar_Syntax_Unionfind.find u in
                      (match uu____1227 with
                       | Some uu____1229 -> true
                       | uu____1230 -> false))))
           ||
           (let uu____1232 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1232
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1238 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1238 with
                    | Some uu____1240 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1245 =
      let uu____1246 = free_names_and_uvars t true in fst uu____1246 in
    uu____1245.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    (((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1257 =
      let uu____1258 = free_names_and_uvars t true in fst uu____1258 in
    uu____1257.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1267 =
      let uu____1268 = free_names_and_uvars t true in fst uu____1268 in
    uu____1267.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1277 =
      let uu____1278 = free_names_and_uvars t true in fst uu____1278 in
    uu____1277.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1288 = free_names_and_uvars t false in snd uu____1288
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1297 =
      let uu____1298 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1298 in
    uu____1297.FStar_Syntax_Syntax.free_names