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
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_names in
    let uu____169 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_uvars
        (Prims.fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____189 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univs
        (Prims.fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____193 =
      FStar_Util.fifo_set_union
        (Prims.fst f1).FStar_Syntax_Syntax.free_univ_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____165;
      FStar_Syntax_Syntax.free_uvars = uu____169;
      FStar_Syntax_Syntax.free_univs = uu____189;
      FStar_Syntax_Syntax.free_univ_names = uu____193
    } in
  let uu____204 = FStar_Util.set_union (Prims.snd f1) (Prims.snd f2) in
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
    | FStar_Syntax_Syntax.U_succ u -> free_univs u
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____232 = free_univs x in union out uu____232)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u -> singleton_univ u
let rec free_names_and_uvs':
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n  ->
                  fun uu____342  ->
                    match uu____342 with
                    | (x,uu____352) ->
                        let uu____353 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n uu____353) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____358 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t) -> singleton_uv (x, t)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____401 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_unknown  ->
          no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
          let f = free_names_and_uvars t use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____422 = free_univs u in union out uu____422)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____428) ->
          let uu____451 = free_names_and_uvars t use_cache in
          aux_binders bs uu____451
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____467 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____467
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____477 = free_names_and_uvars t use_cache in
          aux_binders [(bv, None)] uu____477
      | FStar_Syntax_Syntax.Tm_app (t,args) ->
          let uu____504 = free_names_and_uvars t use_cache in
          free_names_and_uvars_args args uu____504 use_cache
      | FStar_Syntax_Syntax.Tm_match (t,pats) ->
          let uu____536 =
            let uu____553 = free_names_and_uvars t use_cache in
            FStar_List.fold_left
              (fun n  ->
                 fun uu____569  ->
                   match uu____569 with
                   | (p,wopt,t) ->
                       let n1 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t use_cache in
                       let n =
                         let uu____619 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____619
                           (FStar_List.fold_left
                              (fun n  ->
                                 fun x  ->
                                   let uu____633 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n uu____633) n) in
                       let uu____637 = union n1 n2 in union n uu____637)
              uu____553 in
          FStar_All.pipe_right pats uu____536
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,uu____657) ->
          let uu____676 = free_names_and_uvars t1 use_cache in
          let uu____680 = free_names_and_uvars t2 use_cache in
          union uu____676 uu____680
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,uu____686) ->
          let uu____705 = free_names_and_uvars t1 use_cache in
          let uu____709 = free_names_and_uvars_comp c use_cache in
          union uu____705 uu____709
      | FStar_Syntax_Syntax.Tm_let (lbs,t) ->
          let uu____725 =
            let uu____732 = free_names_and_uvars t use_cache in
            FStar_List.fold_left
              (fun n  ->
                 fun lb  ->
                   let uu____744 =
                     let uu____748 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____752 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____748 uu____752 in
                   union n uu____744) uu____732 in
          FStar_All.pipe_right (Prims.snd lbs) uu____725
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern args)
          ->
          let uu____773 = free_names_and_uvars t use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____773
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic (uu____796,t')) ->
          let uu____806 = free_names_and_uvars t use_cache in
          let uu____810 = free_names_and_uvars t' use_cache in
          union uu____806 uu____810
      | FStar_Syntax_Syntax.Tm_meta (t,uu____815) ->
          free_names_and_uvars t use_cache
and free_names_and_uvars:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun t  ->
    fun use_cache  ->
      let t = FStar_Syntax_Subst.compress t in
      let uu____825 = FStar_ST.read t.FStar_Syntax_Syntax.vars in
      match uu____825 with
      | Some n when
          let uu____834 = should_invalidate_cache n use_cache in
          Prims.op_Negation uu____834 ->
          let uu____835 = FStar_Syntax_Syntax.new_fv_set () in (n, uu____835)
      | uu____838 ->
          (FStar_ST.write t.FStar_Syntax_Syntax.vars None;
           (let n = free_names_and_uvs' t use_cache in
            FStar_ST.write t.FStar_Syntax_Syntax.vars (Some (Prims.fst n)); n))
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
             (fun n  ->
                fun uu____877  ->
                  match uu____877 with
                  | (x,uu____889) ->
                      let uu____894 = free_names_and_uvars x use_cache in
                      union n uu____894) acc)
and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n  ->
          fun uu____919  ->
            match uu____919 with
            | (x,uu____929) ->
                let uu____930 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache in
                union n uu____930) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars* FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____938 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____938 with
      | Some n ->
          let uu____947 = should_invalidate_cache n use_cache in
          if uu____947
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____956 = FStar_Syntax_Syntax.new_fv_set () in
             (n, uu____956))
      | uu____959 ->
          let n =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None )|FStar_Syntax_Syntax.Total
              (t,None ) -> free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u)|FStar_Syntax_Syntax.Total
              (t,Some u) ->
                let uu____991 = free_univs u in
                let uu____995 = free_names_and_uvars t use_cache in
                union uu____991 uu____995
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1001 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1001 use_cache in
                FStar_List.fold_left
                  (fun us  ->
                     fun u  ->
                       let uu____1013 = free_univs u in union us uu____1013)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (Prims.fst n)); n)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1024 =
            FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1024
            (FStar_Util.for_some
               (fun uu____1077  ->
                  match uu____1077 with
                  | (u,uu____1087) ->
                      let uu____1100 = FStar_Unionfind.find u in
                      (match uu____1100 with
                       | FStar_Syntax_Syntax.Fixed uu____1107 -> true
                       | uu____1112 -> false))))
           ||
           (let uu____1116 =
              FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1116
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1126 = FStar_Unionfind.find u in
                    match uu____1126 with
                    | Some uu____1129 -> true
                    | None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1134 =
      let uu____1135 = free_names_and_uvars t true in Prims.fst uu____1135 in
    uu____1134.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
      FStar_Unionfind.uvar*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    let uu____1146 =
      let uu____1147 = free_names_and_uvars t true in Prims.fst uu____1147 in
    uu____1146.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1156 =
      let uu____1157 = free_names_and_uvars t true in Prims.fst uu____1157 in
    uu____1156.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1166 =
      let uu____1167 = free_names_and_uvars t true in Prims.fst uu____1167 in
    uu____1166.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____1177 = free_names_and_uvars t false in Prims.snd uu____1177
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1186 =
      let uu____1187 = free_names_and_uvars_binders bs no_free_vars true in
      Prims.fst uu____1187 in
    uu____1186.FStar_Syntax_Syntax.free_names