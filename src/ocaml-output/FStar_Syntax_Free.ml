open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set) =
  let uu____7 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
     FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____7)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let uu____18 =
      let uu____20 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____20 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
       FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____18)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____35 =
      let uu____36 =
        let uu____38 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____38 in
      {
        FStar_Syntax_Syntax.free_names = uu____36;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____42 = FStar_Syntax_Syntax.new_fv_set () in (uu____35, uu____42)
let singleton_uv:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____67 =
      let uu____68 =
        let uu____78 = FStar_Syntax_Syntax.new_uv_set () in
        FStar_Util.set_add x uu____78 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____68;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____98 = FStar_Syntax_Syntax.new_fv_set () in (uu____67, uu____98)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____107 =
      let uu____108 =
        let uu____110 = FStar_Syntax_Syntax.new_universe_uvar_set () in
        FStar_Util.set_add x uu____110 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____108;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____114 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____107, uu____114)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let uu____123 =
      let uu____124 =
        let uu____126 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____126 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____124
      } in
    let uu____134 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____123, uu____134)
let union f1 f2 =
  let uu____164 =
    let uu____165 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_names
        (fst f2).FStar_Syntax_Syntax.free_names in
    let uu____169 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_uvars
        (fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____189 =
      FStar_Util.set_union (fst f1).FStar_Syntax_Syntax.free_univs
        (fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____193 =
      FStar_Util.fifo_set_union (fst f1).FStar_Syntax_Syntax.free_univ_names
        (fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____165;
      FStar_Syntax_Syntax.free_uvars = uu____169;
      FStar_Syntax_Syntax.free_univs = uu____189;
      FStar_Syntax_Syntax.free_univ_names = uu____193
    } in
  let uu____204 = FStar_Util.set_union (snd f1) (snd f2) in
  (uu____164, uu____204)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____215 = FStar_Syntax_Subst.compress_univ u in
    match uu____215 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____219 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____232 = free_univs x in union out uu____232)
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
                  fun uu____354  ->
                    match uu____354 with
                    | (x,uu____364) ->
                        let uu____365 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____365) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____370 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____413 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____415 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____434 = free_univs u in union out uu____434)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____440) ->
          let uu____463 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____463
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____479 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____479
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____489 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____489
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____516 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____516 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____548 =
            let uu____565 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____581  ->
                   match uu____581 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____631 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____631
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____645 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____645) n1) in
                       let uu____649 = union n11 n2 in union n3 uu____649)
              uu____565 in
          FStar_All.pipe_right pats uu____548
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____669) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____748 = union u1 u2 in
               let uu____752 = free_names_and_uvars tac use_cache in
               union uu____748 uu____752)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____768 =
            let uu____775 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____787 =
                     let uu____791 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____795 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____791 uu____795 in
                   union n1 uu____787) uu____775 in
          FStar_All.pipe_right (snd lbs) uu____768
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____816 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____816
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____839,t')) ->
          let uu____849 = free_names_and_uvars t1 use_cache in
          let uu____853 = free_names_and_uvars t' use_cache in
          union uu____849 uu____853
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____858) ->
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
      let uu____868 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____868 with
      | Some n1 when
          let uu____877 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____877 ->
          let uu____878 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____878)
      | uu____881 ->
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
                fun uu____920  ->
                  match uu____920 with
                  | (x,uu____932) ->
                      let uu____937 = free_names_and_uvars x use_cache in
                      union n1 uu____937) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____962  ->
            match uu____962 with
            | (x,uu____972) ->
                let uu____973 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____973) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____981 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____981 with
      | Some n1 ->
          let uu____990 = should_invalidate_cache n1 use_cache in
          if uu____990
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____999 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____999))
      | uu____1002 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u) ->
                let uu____1030 = free_univs u in
                let uu____1034 = free_names_and_uvars t use_cache in
                union uu____1030 uu____1034
            | FStar_Syntax_Syntax.Total (t,Some u) ->
                let uu____1045 = free_univs u in
                let uu____1049 = free_names_and_uvars t use_cache in
                union uu____1045 uu____1049
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1055 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1055 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1067 = free_univs u in union us1 uu____1067)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1078 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1078
            (FStar_Util.for_some
               (fun uu____1131  ->
                  match uu____1131 with
                  | (u,uu____1141) ->
                      let uu____1154 = FStar_Unionfind.find u in
                      (match uu____1154 with
                       | FStar_Syntax_Syntax.Fixed uu____1161 -> true
                       | uu____1166 -> false))))
           ||
           (let uu____1170 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1170
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1180 = FStar_Unionfind.find u in
                    match uu____1180 with
                    | Some uu____1183 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1188 =
      let uu____1189 = free_names_and_uvars t true in fst uu____1189 in
    uu____1188.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
      FStar_Unionfind.uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1200 =
      let uu____1201 = free_names_and_uvars t true in fst uu____1201 in
    uu____1200.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1210 =
      let uu____1211 = free_names_and_uvars t true in fst uu____1211 in
    uu____1210.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1220 =
      let uu____1221 = free_names_and_uvars t true in fst uu____1221 in
    uu____1220.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1231 = free_names_and_uvars t false in snd uu____1231
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1240 =
      let uu____1241 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1241 in
    uu____1240.FStar_Syntax_Syntax.free_names