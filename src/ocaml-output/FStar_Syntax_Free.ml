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
  fun uu____10  ->
    FStar_Util.new_set
      (fun uu____27  ->
         fun uu____28  ->
           match (uu____27, uu____28) with
           | ((x,uu____62),(y,uu____64)) ->
               let uu____97 = FStar_Syntax_Unionfind.uvar_id x in
               let uu____98 = FStar_Syntax_Unionfind.uvar_id y in
               uu____97 - uu____98)
      (fun uu____102  ->
         match uu____102 with
         | (x,uu____112) -> FStar_Syntax_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun uu____126  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____135 = FStar_Syntax_Unionfind.univ_uvar_id x in
           let uu____136 = FStar_Syntax_Unionfind.univ_uvar_id y in
           uu____135 - uu____136)
      (fun x  -> FStar_Syntax_Unionfind.univ_uvar_id x)
let no_uvs: FStar_Syntax_Syntax.uvars = new_uv_set ()
let no_universe_uvars: FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_free_vars:
  (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2
  =
  let uu____147 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = no_uvs;
     FStar_Syntax_Syntax.free_univs = no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, uu____147)
let singleton_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun fv  ->
    let uu____162 =
      let uu____165 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____165 in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = no_uvs;
       FStar_Syntax_Syntax.free_univs = no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, uu____162)
let singleton_bv:
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____180 =
      let uu____181 =
        let uu____184 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Util.set_add x uu____184 in
      {
        FStar_Syntax_Syntax.free_names = uu____181;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____187 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____180, uu____187)
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
    let uu____242 =
      let uu____243 =
        let uu____266 = new_uv_set () in FStar_Util.set_add x uu____266 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____243;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____309 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____242, uu____309)
let singleton_univ:
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____324 =
      let uu____325 =
        let uu____328 = new_universe_uvar_set () in
        FStar_Util.set_add x uu____328 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____325;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      } in
    let uu____331 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____324, uu____331)
let singleton_univ_name:
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____346 =
      let uu____347 =
        let uu____350 = FStar_Syntax_Syntax.new_universe_names_fifo_set () in
        FStar_Util.fifo_set_add x uu____350 in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = no_uvs;
        FStar_Syntax_Syntax.free_univs = no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = uu____347
      } in
    let uu____357 = FStar_Syntax_Syntax.new_fv_set () in
    (uu____346, uu____357)
let union f1 f2 =
  let uu____407 =
    let uu____408 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names in
    let uu____415 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars in
    let uu____462 =
      FStar_Util.set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs in
    let uu____469 =
      FStar_Util.fifo_set_union
        (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
        (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names in
    {
      FStar_Syntax_Syntax.free_names = uu____408;
      FStar_Syntax_Syntax.free_uvars = uu____415;
      FStar_Syntax_Syntax.free_univs = uu____462;
      FStar_Syntax_Syntax.free_univ_names = uu____469
    } in
  let uu____478 =
    FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
      (FStar_Pervasives_Native.snd f2) in
  (uu____407, uu____478)
let rec free_univs:
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2
  =
  fun u  ->
    let uu____497 = FStar_Syntax_Subst.compress_univ u in
    match uu____497 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____504 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____527 = free_univs x in union out uu____527)
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
                  fun uu____693  ->
                    match uu____693 with
                    | (x,uu____711) ->
                        let uu____712 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____712) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____720 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____801 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____803 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____838 = free_univs u in union out uu____838)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____847) ->
          let uu____872 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____872
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____901 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____901
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____918 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____918
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____969 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____969 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____1026 =
            let uu____1055 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____1094  ->
                   match uu____1094 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____1186 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____1186
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____1214 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____1214) n1) in
                       let uu____1221 = union n11 n2 in union n3 uu____1221)
              uu____1055 in
          FStar_All.pipe_right pats uu____1026
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____1256) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____1408 = union u1 u2 in
               let uu____1415 = free_names_and_uvars tac use_cache in
               union uu____1408 uu____1415)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____1444 =
            let uu____1455 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____1479 =
                     let uu____1486 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____1493 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____1486 uu____1493 in
                   union n1 uu____1479) uu____1455 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1444
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____1532 = free_names_and_uvars t1 use_cache in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____1532
      | FStar_Syntax_Syntax.Tm_meta
          (t1,FStar_Syntax_Syntax.Meta_monadic (uu____1576,t')) ->
          let uu____1594 = free_names_and_uvars t1 use_cache in
          let uu____1601 = free_names_and_uvars t' use_cache in
          union uu____1594 uu____1601
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____1609) ->
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
      let uu____1625 = FStar_ST.read t1.FStar_Syntax_Syntax.vars in
      match uu____1625 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____1637 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____1637 ->
          let uu____1638 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____1638)
      | uu____1643 ->
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
                fun uu____1710  ->
                  match uu____1710 with
                  | (x,uu____1732) ->
                      let uu____1741 = free_names_and_uvars x use_cache in
                      union n1 uu____1741) acc)
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
                fun uu____1779  ->
                  match uu____1779 with
                  | (x,uu____1797) ->
                      let uu____1798 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1798) acc)
and free_names_and_uvars_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars,FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun use_cache  ->
      let uu____1811 = FStar_ST.read c.FStar_Syntax_Syntax.vars in
      match uu____1811 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1823 = should_invalidate_cache n1 use_cache in
          if uu____1823
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1834 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1834))
      | uu____1839 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1889 = free_univs u in
                let uu____1896 = free_names_and_uvars t use_cache in
                union uu____1889 uu____1896
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1915 = free_univs u in
                let uu____1922 = free_names_and_uvars t use_cache in
                union uu____1915 uu____1922
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1931 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1931 use_cache in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1955 = free_univs u in union us1 uu____1955)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and should_invalidate_cache:
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let uu____1971 =
            FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements in
          FStar_All.pipe_right uu____1971
            (FStar_Util.for_some
               (fun uu____2093  ->
                  match uu____2093 with
                  | (u,uu____2103) ->
                      let uu____2112 = FStar_Syntax_Unionfind.find u in
                      (match uu____2112 with
                       | FStar_Pervasives_Native.Some uu____2115 -> true
                       | uu____2116 -> false))))
           ||
           (let uu____2120 =
              FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements in
            FStar_All.pipe_right uu____2120
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____2133 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____2133 with
                    | FStar_Pervasives_Native.Some uu____2136 -> true
                    | FStar_Pervasives_Native.None  -> false))))
let names: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    let uu____2143 =
      let uu____2144 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2144 in
    uu____2143.FStar_Syntax_Syntax.free_names
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
    let uu____2163 =
      let uu____2164 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2164 in
    uu____2163.FStar_Syntax_Syntax.free_uvars
let univs:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    let uu____2179 =
      let uu____2180 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2180 in
    uu____2179.FStar_Syntax_Syntax.free_univs
let univnames:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    let uu____2195 =
      let uu____2196 = free_names_and_uvars t true in
      FStar_Pervasives_Native.fst uu____2196 in
    uu____2195.FStar_Syntax_Syntax.free_univ_names
let fvars: FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  ->
    let uu____2211 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____2211
let names_of_binders:
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    let uu____2226 =
      let uu____2227 = free_names_and_uvars_binders bs no_free_vars true in
      FStar_Pervasives_Native.fst uu____2227 in
    uu____2226.FStar_Syntax_Syntax.free_names