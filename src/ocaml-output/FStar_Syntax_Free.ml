open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
let new_uv_set:
  Prims.unit ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term'
                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun uu____7  ->
    FStar_Util.new_set
      (fun uu____19  ->
         fun uu____20  ->
           match (uu____19, uu____20) with
           | ((x,uu____34),(y,uu____36)) ->
               let uu____47 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____48 = FStar_Syntax_Unionfind.uvar_id y in
               uu____47 - uu____48)
      (fun uu____52  ->
         match uu____52 with
         | (x,uu____57) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____64  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____72 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____73 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____72 - uu____73)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
  =
  let uu____80 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____80)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun fv  ->
    let uu____92 =
      let uu____94 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____94 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____92)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____106 =
      let uu____107 =
        let uu____109 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____109 in
      {
        FStar_Syntax_Syntax.free_names = uu____107;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____113 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____106, uu____113)
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
    let uu____139 =
      let uu____140 =
        let uu____150 = new_uv_set () in FStar_Util.set_add x uu____150 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____140;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____170 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____139, uu____170)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____180 =
      let uu____181 =
        let uu____183 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____183 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____181;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____187 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____180, uu____187)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____197 =
      let uu____198 =
        let uu____200 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____200 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____198
      } in
    let uu____208 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____197, uu____208)
let union f1 f2 =
  let uu____241 =
    let uu____242 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names in
    let uu____246 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____266 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____270 =
      FStar_Util.fifo_set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____242;
      FStar_Syntax_Syntax.free_uvars = uu____246;
      FStar_Syntax_Syntax.free_univs = uu____266;
      FStar_Syntax_Syntax.free_univ_names = uu____270
    } in
  let uu____281 =
    FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
      (FStar_Pervasives_Native.snd f2) in
  (uu____241, uu____281)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____293 = FStar_Syntax_Subst.compress_univ u in
    match uu____293 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____297 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____313 = free_univs x in union out uu____313)
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
                  fun uu____416  ->
                    match uu____416 with
                    | (x,uu____426) ->
                        let uu____427 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____427) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____432 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____467 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____469 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____489 = free_univs u in union out uu____489)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____495) ->
          let uu____506 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____506
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____520 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____520
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____528 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____528
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____551 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____551 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____575 =
            let uu____589 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____612  ->
                   match uu____612 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____653 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____653
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____670 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____670) n1) in
                       let uu____674 = union n11 n2 in union n3 uu____674)
              uu____589 in
          FStar_All.pipe_right pats uu____575
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____691) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____747 = union u1 u2 in
               let uu____751 = free_names_and_uvars tac use_cache in
               union uu____747 uu____751)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____765 =
            let uu____772 = free_names_and_uvars t1 use_cache in
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
                   union n1 uu____787) uu____772 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____765
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____813 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____813
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____836,t')) ->
          let uu____842 = free_names_and_uvars t1 use_cache in
          let uu____846 = free_names_and_uvars t' use_cache in
          union uu____842 uu____846
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____851) ->
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
      let uu____858 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____858 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____867 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____867 ->
          let uu____868 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____868)
      | uu____871 ->
          (FStar_ST.write t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.write t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))
and free_names_and_uvars_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
                fun uu____912  ->
                  match uu____912 with
                  | (x,uu____923) ->
                      let uu____926 = free_names_and_uvars x use_cache in
                      union n1 uu____926) acc)
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
                fun uu____950  ->
                  match uu____950 with
                  | (x,uu____960) ->
                      let uu____961 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____961) acc)
and free_names_and_uvars_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____968 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____968 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____977 = should_invalidate_cache n1 use_cache in
          if uu____977
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____986 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____986))
      | uu____989 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1011 = free_univs u in
                let uu____1015 = free_names_and_uvars t use_cache in
                union uu____1011 uu____1015
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1024 = free_univs u in
                let uu____1028 = free_names_and_uvars t use_cache in
                union uu____1024 uu____1028
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1034 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1034 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1049 = free_univs u in union us1 uu____1049)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1062 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1062
            (FStar_Util.for_some
               (fun uu____1115  ->
                  match uu____1115 with
                  | (u,uu____1120) ->
                      let uu____1123 = FStar_Syntax_Unionfind.find u in
                      (match uu____1123 with
                       | FStar_Pervasives_Native.Some uu____1125 -> true
                       | uu____1126 -> false))))
           ||
           (let uu____1129 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____1129
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1138 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1138 with
                    | FStar_Pervasives_Native.Some uu____1140 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____1146 =
      let uu____1147 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1147 in
    uu____1146.FStar_Syntax_Syntax.free_names
let uvars:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term'
                                        FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun t  ->
    let uu____1159 =
      let uu____1160 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1160 in
    uu____1159.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____1170 =
      let uu____1171 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1171 in
    uu____1170.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____1181 =
      let uu____1182 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____1182 in
    uu____1181.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____1193 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1193
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____1203 =
      let uu____1204 = free_names_and_uvars_binders bs no_free_vars true in
      FStar_Pervasives_Native.fst uu____1204 in
    uu____1203.FStar_Syntax_Syntax.free_names