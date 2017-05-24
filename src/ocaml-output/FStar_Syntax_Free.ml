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
    | FStar_Syntax_Syntax.U_zero 
      |FStar_Syntax_Syntax.U_bvar _|FStar_Syntax_Syntax.U_unknown  ->
        no_free_vars
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
                  fun uu____342  ->
                    match uu____342 with
                    | (x,uu____352) ->
                        let uu____353 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____353) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____358 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____401 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_unknown  ->
          no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____422 = free_univs u in union out uu____422)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____428) ->
          let uu____451 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____451
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____467 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____467
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____477 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, None)] uu____477
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____504 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____504 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____536 =
            let uu____553 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____569  ->
                   match uu____569 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____619 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____619
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____633 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____633) n1) in
                       let uu____637 = union n11 n2 in union n3 uu____637)
              uu____553 in
          FStar_All.pipe_right pats uu____536
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____657) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match snd asc with
           | None  -> union u1 u2
           | Some tac ->
               let uu____736 = union u1 u2 in
               let uu____740 = free_names_and_uvars tac use_cache in
               union uu____736 uu____740)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____756 =
            let uu____763 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____775 =
                     let uu____779 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____783 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____779 uu____783 in
                   union n1 uu____775) uu____763 in
          FStar_All.pipe_right (snd lbs) uu____756
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____804 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____804
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____827,t')) ->
          let uu____837 = free_names_and_uvars t1 use_cache in
          let uu____841 = free_names_and_uvars t' use_cache in
          union uu____837 uu____841
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____846) ->
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
      let uu____856 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____856 with
      | Some n1 when
          let uu____865 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____865 ->
          let uu____866 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____866)
      | uu____869 ->
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
                fun uu____908  ->
                  match uu____908 with
                  | (x,uu____920) ->
                      let uu____925 = free_names_and_uvars x use_cache in
                      union n1 uu____925) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n1  ->
          fun uu____950  ->
            match uu____950 with
            | (x,uu____960) ->
                let uu____961 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n1 uu____961) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____969 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____969 with
      | Some n1 ->
          let uu____978 = should_invalidate_cache n1 use_cache in
          if uu____978
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____987 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____987))
      | uu____990 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None )|FStar_Syntax_Syntax.Total
              (t,None ) -> free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u)|FStar_Syntax_Syntax.Total
              (t,Some u) ->
                let uu____1022 = free_univs u in
                let uu____1026 = free_names_and_uvars t use_cache in
                union uu____1022 uu____1026
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1032 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1032 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1044 = free_univs u in union us1 uu____1044)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (fst n1)); n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1055 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1055
            (FStar_Util.for_some
               (fun uu____1108  ->
                  match uu____1108 with
                  | (u,uu____1118) ->
                      let uu____1131 = FStar_Unionfind.find u in
                      (match uu____1131 with
                       | FStar_Syntax_Syntax.Fixed uu____1138 -> true
                       | uu____1143 -> false))))
           ||
           (let uu____1147 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1147
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1157 = FStar_Unionfind.find u in
                    match uu____1157 with
                    | Some uu____1160 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1165 =
      let uu____1166 = free_names_and_uvars t true in fst uu____1166 in
    uu____1165.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
      FStar_Unionfind.uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1177 =
      let uu____1178 = free_names_and_uvars t true in fst uu____1178 in
    uu____1177.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1187 =
      let uu____1188 = free_names_and_uvars t true in fst uu____1188 in
    uu____1187.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1197 =
      let uu____1198 = free_names_and_uvars t true in fst uu____1198 in
    uu____1197.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> let uu____1208 = free_names_and_uvars t false in snd uu____1208
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1217 =
      let uu____1218 = free_names_and_uvars_binders bs no_free_vars true in
      fst uu____1218 in
    uu____1217.FStar_Syntax_Syntax.free_names