open Prims
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Env.AllowUnboundUniverses]
let (tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc, uvs, tps, k, mutuals, data) ->
          let env0 = env in
          let uu____50 = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu____50 with
           | (usubst, uvs1) ->
               let uu____77 =
                 let uu____84 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu____85 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu____86 =
                   let uu____87 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst in
                   FStar_Syntax_Subst.subst uu____87 k in
                 (uu____84, uu____85, uu____86) in
               (match uu____77 with
                | (env1, tps1, k1) ->
                    let uu____107 = FStar_Syntax_Subst.open_term tps1 k1 in
                    (match uu____107 with
                     | (tps2, k2) ->
                         let uu____122 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2 in
                         (match uu____122 with
                          | (tps3, env_tps, guard_params, us) ->
                              let uu____143 =
                                let uu____162 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2 in
                                match uu____162 with
                                | (k3, uu____188, g) ->
                                    let k4 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Exclude
                                           FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Zeta;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3 in
                                    let uu____191 =
                                      FStar_Syntax_Util.arrow_formals k4 in
                                    let uu____206 =
                                      let uu____207 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____207 in
                                    (uu____191, uu____206) in
                              (match uu____143 with
                               | ((indices, t), guard) ->
                                   let k3 =
                                     let uu____270 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow indices
                                       uu____270 in
                                   let uu____273 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____273 with
                                    | (t_type, u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____291 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq) in
                                              Prims.op_Negation uu____291))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type) in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____298 =
                                              let uu____304 =
                                                let uu____306 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                let uu____308 =
                                                  FStar_Ident.string_of_lid
                                                    tc in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____306 uu____308 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____304) in
                                            FStar_Errors.raise_error
                                              uu____298
                                              s.FStar_Syntax_Syntax.sigrng)
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1 in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 tps3 guard in
                                          let t_tc =
                                            let uu____321 =
                                              let uu____330 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1) in
                                              let uu____347 =
                                                let uu____356 =
                                                  let uu____369 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1 in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____369 in
                                                FStar_All.pipe_right indices
                                                  uu____356 in
                                              FStar_List.append uu____330
                                                uu____347 in
                                            let uu____392 =
                                              let uu____395 =
                                                let uu____396 =
                                                  let uu____401 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1 in
                                                  FStar_Syntax_Subst.subst
                                                    uu____401 in
                                                FStar_All.pipe_right t
                                                  uu____396 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____395 in
                                            FStar_Syntax_Util.arrow uu____321
                                              uu____392 in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3 in
                                          let uu____418 =
                                            let uu____423 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4 in
                                            let uu____424 =
                                              let uu____425 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1 in
                                              FStar_Syntax_Subst.subst
                                                uu____425 k4 in
                                            (uu____423, uu____424) in
                                          match uu____418 with
                                          | (tps5, k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None in
                                              let uu____445 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc) in
                                              (uu____445,
                                                (let uu___61_451 = s in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____456 -> failwith "impossible"
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t))
  =
  fun env ->
    fun tcs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (c, _uvs, t, tc_lid, ntps, _mutual_tcs) ->
            let uu____520 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu____520 with
             | (usubst, _uvs1) ->
                 let uu____543 =
                   let uu____548 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu____549 = FStar_Syntax_Subst.subst usubst t in
                   (uu____548, uu____549) in
                 (match uu____543 with
                  | (env1, t1) ->
                      let uu____556 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____595 ->
                               match uu____595 with
                               | (se1, u_tc) ->
                                   let uu____610 =
                                     let uu____612 =
                                       let uu____613 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____613 in
                                     FStar_Ident.lid_equals tc_lid uu____612 in
                                   if uu____610
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____633, uu____634, tps,
                                           uu____636, uu____637, uu____638)
                                          ->
                                          let tps1 =
                                            let uu____648 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu____648
                                              (FStar_List.map
                                                 (fun uu____688 ->
                                                    match uu____688 with
                                                    | (x, uu____702) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag)))) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu____710 =
                                            let uu____717 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu____717, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu____710
                                      | uu____724 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu____767 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu____767
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu____556 with
                       | (env2, tps, u_tc) ->
                           let uu____799 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu____815 =
                               let uu____816 = FStar_Syntax_Subst.compress t2 in
                               uu____816.FStar_Syntax_Syntax.n in
                             match uu____815 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu____855 = FStar_Util.first_N ntps bs in
                                 (match uu____855 with
                                  | (uu____896, bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      let subst1 =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i ->
                                                fun uu____967 ->
                                                  match uu____967 with
                                                  | (x, uu____976) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x))) in
                                      let uu____983 =
                                        FStar_Syntax_Subst.subst subst1 t3 in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____983)
                             | uu____984 -> ([], t2) in
                           (match uu____799 with
                            | (arguments, result) ->
                                ((let uu____1028 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu____1028
                                  then
                                    let uu____1031 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu____1033 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu____1036 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1031 uu____1033 uu____1036
                                  else ());
                                 (let uu____1041 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu____1041 with
                                  | (arguments1, env', us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          FStar_Pervasives_Native.None
                                          result.FStar_Syntax_Syntax.pos in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc in
                                      let uu____1059 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result in
                                      (match uu____1059 with
                                       | (result1, res_lcomp) ->
                                           let uu____1070 =
                                             FStar_Syntax_Util.head_and_args
                                               result1 in
                                           (match uu____1070 with
                                            | (head1, args) ->
                                                let p_args =
                                                  let uu____1128 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1128 in
                                                (FStar_List.iter2
                                                   (fun uu____1210 ->
                                                      fun uu____1211 ->
                                                        match (uu____1210,
                                                                uu____1211)
                                                        with
                                                        | ((bv, uu____1241),
                                                           (t2, uu____1243))
                                                            ->
                                                            let uu____1270 =
                                                              let uu____1271
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2 in
                                                              uu____1271.FStar_Syntax_Syntax.n in
                                                            (match uu____1270
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1275 ->
                                                                 let uu____1276
                                                                   =
                                                                   let uu____1282
                                                                    =
                                                                    let uu____1284
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu____1286
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1284
                                                                    uu____1286 in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1282) in
                                                                 FStar_Errors.raise_error
                                                                   uu____1276
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1291 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ in
                                                    FStar_All.pipe_right
                                                      uu____1291
                                                      FStar_Syntax_Util.unrefine in
                                                  (let uu____1293 =
                                                     let uu____1294 =
                                                       FStar_Syntax_Subst.compress
                                                         ty in
                                                     uu____1294.FStar_Syntax_Syntax.n in
                                                   match uu____1293 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1297 -> ()
                                                   | uu____1298 ->
                                                       let uu____1299 =
                                                         let uu____1305 =
                                                           let uu____1307 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1 in
                                                           let uu____1309 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1307
                                                             uu____1309 in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1305) in
                                                       FStar_Errors.raise_error
                                                         uu____1299
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1314 =
                                                       let uu____1315 =
                                                         FStar_Syntax_Subst.compress
                                                           head1 in
                                                       uu____1315.FStar_Syntax_Syntax.n in
                                                     match uu____1314 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1319;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1320;_},
                                                          tuvs)
                                                         when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         if
                                                           (FStar_List.length
                                                              _uvs1)
                                                             =
                                                             (FStar_List.length
                                                                tuvs)
                                                         then
                                                           FStar_List.fold_left2
                                                             (fun g ->
                                                                fun u1 ->
                                                                  fun u2 ->
                                                                    let uu____1334
                                                                    =
                                                                    let uu____1335
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    let uu____1336
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____1335
                                                                    uu____1336 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1334)
                                                             FStar_TypeChecker_Env.trivial_guard
                                                             tuvs _uvs1
                                                         else
                                                           FStar_Errors.raise_error
                                                             (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                               "Length of annotated universes does not match inferred universes")
                                                             se.FStar_Syntax_Syntax.sigrng
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         FStar_TypeChecker_Env.trivial_guard
                                                     | uu____1342 ->
                                                         let uu____1343 =
                                                           let uu____1349 =
                                                             let uu____1351 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid in
                                                             let uu____1353 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1 in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1351
                                                               uu____1353 in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1349) in
                                                         FStar_Errors.raise_error
                                                           uu____1343
                                                           se.FStar_Syntax_Syntax.sigrng in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g ->
                                                          fun uu____1371 ->
                                                            fun u_x ->
                                                              match uu____1371
                                                              with
                                                              | (x,
                                                                 uu____1380)
                                                                  ->
                                                                  let uu____1385
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1385)
                                                       g_uvs arguments1 us in
                                                   let t2 =
                                                     let uu____1389 =
                                                       let uu____1398 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1438
                                                                 ->
                                                                 match uu____1438
                                                                 with
                                                                 | (x,
                                                                    uu____1452)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                       FStar_List.append
                                                         uu____1398
                                                         arguments1 in
                                                     let uu____1466 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1 in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1389 uu____1466 in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2 in
                                                   ((let uu___183_1471 = se in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____1475 -> failwith "impossible"
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
          Prims.list))
  =
  fun env ->
    fun tcs ->
      fun datas ->
        let binders =
          FStar_All.pipe_right tcs
            (FStar_List.map
               (fun uu____1566 ->
                  match uu____1566 with
                  | (se, uu____1572) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1573, uu____1574, tps, k, uu____1577,
                            uu____1578)
                           ->
                           let uu____1587 =
                             let uu____1588 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1588 in
                           FStar_Syntax_Syntax.null_binder uu____1587
                       | uu____1593 -> failwith "Impossible"))) in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1622, uu____1623, t, uu____1625, uu____1626,
                       uu____1627)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1634 -> failwith "Impossible")) in
        let t =
          let uu____1639 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1639 in
        (let uu____1649 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu____1649
         then
           let uu____1654 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1654
         else ());
        (let uu____1659 = FStar_TypeChecker_Util.generalize_universes env t in
         match uu____1659 with
         | (uvs, t1) ->
             ((let uu____1679 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu____1679
               then
                 let uu____1684 =
                   let uu____1686 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u -> u.FStar_Ident.idText)) in
                   FStar_All.pipe_right uu____1686 (FStar_String.concat ", ") in
                 let uu____1703 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1684 uu____1703
               else ());
              (let uu____1708 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu____1708 with
               | (uvs1, t2) ->
                   let uu____1723 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu____1723 with
                    | (args, uu____1747) ->
                        let uu____1768 =
                          FStar_Util.first_N (FStar_List.length binders) args in
                        (match uu____1768 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1873 ->
                                    fun uu____1874 ->
                                      match (uu____1873, uu____1874) with
                                      | ((x, uu____1896), (se, uu____1898))
                                          ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu____1914, tps,
                                                uu____1916, mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu____1928 =
                                                 let uu____1933 =
                                                   let uu____1934 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu____1934.FStar_Syntax_Syntax.n in
                                                 match uu____1933 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu____1963 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1 in
                                                     (match uu____1963 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2041 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu____2060 -> ([], ty) in
                                               (match uu____1928 with
                                                | (tps1, t3) ->
                                                    let uu___260_2069 = se in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigattrs)
                                                    })
                                           | uu____2074 ->
                                               failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2081 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _2085 ->
                                             FStar_Syntax_Syntax.U_name _2085)) in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2104 ->
                                             match uu___0_2104 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu____2110,
                                                    uu____2111, uu____2112,
                                                    uu____2113, uu____2114);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2115;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2116;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2117;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2118;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2131 ->
                                                 failwith "Impossible")) in
                                   FStar_List.map2
                                     (fun uu____2155 ->
                                        fun d ->
                                          match uu____2155 with
                                          | (t3, uu____2164) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu____2170,
                                                    uu____2171, tc, ntps,
                                                    mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2182 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_All.pipe_right
                                                       uu____2182
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   let uu___296_2183 = d in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___296_2183.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___296_2183.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___296_2183.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___296_2183.FStar_Syntax_Syntax.sigattrs)
                                                   }
                                               | uu____2187 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env ->
    fun s ->
      let uu____2206 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____2206
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____2228 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____2228
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t ->
    let uu____2245 =
      let uu____2246 = FStar_Syntax_Subst.compress t in
      uu____2246.FStar_Syntax_Syntax.n in
    match uu____2245 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2265 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2271 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid ->
    fun arrghs ->
      fun unfolded ->
        fun env ->
          let uu____2308 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2357 ->
               match uu____2357 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2401 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2401 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2308
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          (let uu____2606 =
             let uu____2608 = FStar_Syntax_Print.term_to_string btype in
             Prims.op_Hat "Checking strict positivity in type: " uu____2608 in
           debug_log env uu____2606);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype in
           (let uu____2613 =
              let uu____2615 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____2615 in
            debug_log env uu____2613);
           (let uu____2620 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2620) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2633 =
                  let uu____2634 = FStar_Syntax_Subst.compress btype1 in
                  uu____2634.FStar_Syntax_Syntax.n in
                match uu____2633 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let uu____2664 = try_get_fv t in
                    (match uu____2664 with
                     | (fv, us) ->
                         let uu____2672 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid in
                         if uu____2672
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2688 ->
                                 match uu____2688 with
                                 | (t1, uu____2697) ->
                                     let uu____2702 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2702) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let check_comp1 =
                        let c1 =
                          let uu____2737 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu____2737
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2741 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu____2741
                             (FStar_List.existsb
                                (fun q -> q = FStar_Syntax_Syntax.TotalEffect))) in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2768 ->
                               match uu____2768 with
                               | (b, uu____2777) ->
                                   let uu____2782 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2782) sbs)
                           &&
                           ((let uu____2788 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2788 with
                             | (uu____2794, return_type) ->
                                 let uu____2796 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2796)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2797 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2801 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2806) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2814) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2821, branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2880 ->
                          match uu____2880 with
                          | (p, uu____2893, t) ->
                              let bs =
                                let uu____2912 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2912 in
                              let uu____2921 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2921 with
                               | (bs1, t1) ->
                                   let uu____2929 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2929)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2931, uu____2932)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2975 ->
                    ((let uu____2977 =
                        let uu____2979 =
                          let uu____2981 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2983 =
                            let uu____2985 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.op_Hat " and term: " uu____2985 in
                          Prims.op_Hat uu____2981 uu____2983 in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____2979 in
                      debug_log env uu____2977);
                     false)))))
and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun ilid ->
      fun us ->
        fun args ->
          fun unfolded ->
            fun env ->
              (let uu____2998 =
                 let uu____3000 =
                   let uu____3002 =
                     let uu____3004 = FStar_Syntax_Print.args_to_string args in
                     Prims.op_Hat " applied to arguments: " uu____3004 in
                   Prims.op_Hat ilid.FStar_Ident.str uu____3002 in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____3000 in
               debug_log env uu____2998);
              (let uu____3008 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____3008 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3027 =
                       let uu____3029 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3029
                         FStar_Parser_Const.assume_strictly_positive_attr_lid in
                     (if uu____3027
                      then
                        ((let uu____3033 =
                            let uu____3035 = FStar_Ident.string_of_lid ilid in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____3035 in
                          debug_log env uu____3033);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____3046 =
                        already_unfolded ilid args unfolded env in
                      if uu____3046
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____3057 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu____3057 in
                         (let uu____3063 =
                            let uu____3065 =
                              let uu____3067 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.op_Hat uu____3067
                                ", also adding to the memo table" in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____3065 in
                          debug_log env uu____3063);
                         (let uu____3072 =
                            let uu____3073 = FStar_ST.op_Bang unfolded in
                            let uu____3099 =
                              let uu____3106 =
                                let uu____3111 =
                                  let uu____3112 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3112 in
                                (ilid, uu____3111) in
                              [uu____3106] in
                            FStar_List.append uu____3073 uu____3099 in
                          FStar_ST.op_Colon_Equals unfolded uu____3072);
                         FStar_List.for_all
                           (fun d ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))
and (ty_nested_positive_in_dlid :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun dlid ->
      fun ilid ->
        fun us ->
          fun args ->
            fun num_ibs ->
              fun unfolded ->
                fun env ->
                  debug_log env
                    (Prims.op_Hat
                       "Checking nested positivity in data constructor "
                       (Prims.op_Hat dlid.FStar_Ident.str
                          (Prims.op_Hat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____3211 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3211 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3234 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Env.Iota;
                             FStar_TypeChecker_Env.Zeta;
                             FStar_TypeChecker_Env.AllowUnboundUniverses] env
                             dt in
                         (let uu____3238 =
                            let uu____3240 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____3240 in
                          debug_log env uu____3238);
                         (let uu____3243 =
                            let uu____3244 = FStar_Syntax_Subst.compress dt1 in
                            uu____3244.FStar_Syntax_Syntax.n in
                          match uu____3243 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3272 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____3272 with
                                | (ibs, dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____3336 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3336 dbs1 in
                                    let c1 =
                                      let uu____3340 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3340 c in
                                    let uu____3343 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____3343 with
                                     | (args1, uu____3378) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1 ->
                                                fun ib ->
                                                  fun arg ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((FStar_Pervasives_Native.fst
                                                             ib),
                                                           (FStar_Pervasives_Native.fst
                                                              arg))]) [] ibs1
                                             args1 in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2 in
                                         let c2 =
                                           let uu____3470 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3470 c1 in
                                         ((let uu____3480 =
                                             let uu____3482 =
                                               let uu____3484 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____3487 =
                                                 let uu____3489 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.op_Hat ", and c: "
                                                   uu____3489 in
                                               Prims.op_Hat uu____3484
                                                 uu____3487 in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3482 in
                                           debug_log env uu____3480);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3503 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3506 =
                                  let uu____3507 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____3507.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____3506
                                  ilid num_ibs unfolded env))))))
and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun t ->
      fun ilid ->
        fun num_ibs ->
          fun unfolded ->
            fun env ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t1, args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____3546 = try_get_fv t1 in
                    match uu____3546 with
                    | (fv, uu____3553) ->
                        let uu____3554 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____3554
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  ((let uu____3586 =
                      let uu____3588 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3588 in
                    debug_log env uu____3586);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3593 =
                      FStar_List.fold_left
                        (fun uu____3614 ->
                           fun b ->
                             match uu____3614 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3645 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3649 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3645, uu____3649))) (true, env)
                        sbs1 in
                    match uu____3593 with | (b, uu____3667) -> b))
              | uu____3670 ->
                  failwith "Nested positive check, unhandled case"
let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid ->
    fun dlid ->
      fun ty_bs ->
        fun us ->
          fun unfolded ->
            fun env ->
              let uu____3706 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3706 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3729 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3732 =
                      let uu____3734 = FStar_Syntax_Print.term_to_string dt in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____3734 in
                    debug_log env uu____3732);
                   (let uu____3737 =
                      let uu____3738 = FStar_Syntax_Subst.compress dt in
                      uu____3738.FStar_Syntax_Syntax.n in
                    match uu____3737 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3742 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3747) ->
                        let dbs1 =
                          let uu____3777 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3777 in
                        let dbs2 =
                          let uu____3827 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3827 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3832 =
                            let uu____3834 =
                              let uu____3836 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.op_Hat uu____3836 " binders" in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3834 in
                          debug_log env uu____3832);
                         (let uu____3846 =
                            FStar_List.fold_left
                              (fun uu____3867 ->
                                 fun b ->
                                   match uu____3867 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3898 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3902 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3898, uu____3902)))
                              (true, env) dbs3 in
                          match uu____3846 with | (b, uu____3920) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3923, uu____3924) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3960 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3983 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____3999, uu____4000, uu____4001) ->
            (lid, us, bs)
        | uu____4010 -> failwith "Impossible!" in
      match uu____3983 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____4022 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____4022 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____4046 =
                 let uu____4049 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____4049 in
               FStar_List.for_all
                 (fun d ->
                    let uu____4063 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4063
                      unfolded_inductives env2) uu____4046)
let (check_exn_positivity :
  FStar_Ident.lid -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun data_ctor_lid ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] []
        unfolded_inductives env
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4098, uu____4099, t, uu____4101, uu____4102, uu____4103) -> t
    | uu____4110 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = lid.FStar_Ident.str in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____4127 =
         let uu____4129 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____4129 haseq_suffix in
       uu____4127 = (Prims.parse_int "0"))
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____4139 =
      let uu____4142 =
        let uu____4145 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix) in
        [uu____4145] in
      FStar_List.append lid.FStar_Ident.ns uu____4142 in
    FStar_Ident.lid_of_ids uu____4139
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident * FStar_Syntax_Syntax.term *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.term))
  =
  fun en ->
    fun ty ->
      fun usubst ->
        fun us ->
          let uu____4191 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4205, bs, t, uu____4208, uu____4209) ->
                (lid, bs, t)
            | uu____4218 -> failwith "Impossible!" in
          match uu____4191 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____4241 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____4241 t in
              let uu____4250 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____4250 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____4268 =
                       let uu____4269 = FStar_Syntax_Subst.compress t2 in
                       uu____4269.FStar_Syntax_Syntax.n in
                     match uu____4268 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4273) -> ibs
                     | uu____4294 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____4303 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____4304 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4303 uu____4304 in
                   let ind1 =
                     let uu____4310 =
                       let uu____4315 =
                         FStar_List.map
                           (fun uu____4332 ->
                              match uu____4332 with
                              | (bv, aq) ->
                                  let uu____4351 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____4351, aq)) bs2 in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4315 in
                     uu____4310 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____4357 =
                       let uu____4362 =
                         FStar_List.map
                           (fun uu____4379 ->
                              match uu____4379 with
                              | (bv, aq) ->
                                  let uu____4398 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____4398, aq)) ibs1 in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4362 in
                     uu____4357 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____4404 =
                       let uu____4409 =
                         let uu____4410 = FStar_Syntax_Syntax.as_arg ind2 in
                         [uu____4410] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4409 in
                     uu____4404 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____4459 =
                            let uu____4460 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____4460 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4459) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____4473 =
                              let uu____4476 =
                                let uu____4481 =
                                  let uu____4482 =
                                    let uu____4491 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b) in
                                    FStar_Syntax_Syntax.as_arg uu____4491 in
                                  [uu____4482] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4481 in
                              uu____4476 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____4473)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___630_4514 = fml in
                     let uu____4515 =
                       let uu____4516 =
                         let uu____4523 =
                           let uu____4524 =
                             let uu____4545 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu____4550 =
                               let uu____4563 =
                                 let uu____4574 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____4574] in
                               [uu____4563] in
                             (uu____4545, uu____4550) in
                           FStar_Syntax_Syntax.Meta_pattern uu____4524 in
                         (fml, uu____4523) in
                       FStar_Syntax_Syntax.Tm_meta uu____4516 in
                     {
                       FStar_Syntax_Syntax.n = uu____4515;
                       FStar_Syntax_Syntax.pos =
                         (uu___630_4514.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___630_4514.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4643 =
                              let uu____4648 =
                                let uu____4649 =
                                  let uu____4658 =
                                    let uu____4659 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4659 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____4658 in
                                [uu____4649] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4648 in
                            uu____4643 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4712 =
                              let uu____4717 =
                                let uu____4718 =
                                  let uu____4727 =
                                    let uu____4728 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4728 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____4727 in
                                [uu____4718] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4717 in
                            uu____4712 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2 in
                   let axiom_lid = get_haseq_axiom_lid lid in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid ->
    fun data ->
      fun usubst ->
        fun bs ->
          let dt = datacon_typ data in
          let dt1 = FStar_Syntax_Subst.subst usubst dt in
          let uu____4803 =
            let uu____4804 = FStar_Syntax_Subst.compress dt1 in
            uu____4804.FStar_Syntax_Syntax.n in
          match uu____4803 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4808) ->
              let dbs1 =
                let uu____4838 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4838 in
              let dbs2 =
                let uu____4888 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4888 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4903 =
                           let uu____4908 =
                             let uu____4909 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____4909] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4908 in
                         uu____4903 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4940 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____4940 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4948 =
                       let uu____4953 =
                         let uu____4954 =
                           let uu____4963 =
                             let uu____4964 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4964
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____4963 in
                         [uu____4954] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4953 in
                     uu____4948 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5011 -> FStar_Syntax_Util.t_true
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
              FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax))
  =
  fun all_datas_in_the_bundle ->
    fun usubst ->
      fun us ->
        fun acc ->
          fun ty ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid, uu____5102, uu____5103, uu____5104, uu____5105,
                   uu____5106)
                  -> lid
              | uu____5115 -> failwith "Impossible!" in
            let uu____5117 = acc in
            match uu____5117 with
            | (uu____5154, en, uu____5156, uu____5157) ->
                let uu____5178 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____5178 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____5215 = acc in
                     (match uu____5215 with
                      | (l_axioms, env, guard', cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs in
                          let t_datas =
                            FStar_List.filter
                              (fun s ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____5290, uu____5291, uu____5292,
                                      t_lid, uu____5294, uu____5295)
                                     -> t_lid = lid
                                 | uu____5302 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5317 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5317)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5320 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5323 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5320, uu____5323)))
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          let uu____5381 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5391, us, uu____5393, t, uu____5395, uu____5396) ->
                (us, t)
            | uu____5405 -> failwith "Impossible!" in
          match uu____5381 with
          | (us, t) ->
              let uu____5415 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____5415 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     let uu____5441 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu____5441 with
                     | (axioms, env2, guard, cond) ->
                         let phi =
                           let uu____5519 = FStar_Syntax_Util.arrow_formals t in
                           match uu____5519 with
                           | (uu____5534, t1) ->
                               let uu____5556 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu____5556
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu____5561 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                         (match uu____5561 with
                          | (phi1, uu____5569) ->
                              ((let uu____5571 =
                                  FStar_TypeChecker_Env.should_verify env2 in
                                if uu____5571
                                then
                                  let uu____5574 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5574
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l ->
                                       fun uu____5592 ->
                                         match uu____5592 with
                                         | (lid, fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml in
                                             FStar_List.append l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       (lid, us1, fml1));
                                                  FStar_Syntax_Syntax.sigrng
                                                    = FStar_Range.dummyRange;
                                                  FStar_Syntax_Syntax.sigquals
                                                    = [];
                                                  FStar_Syntax_Syntax.sigmeta
                                                    =
                                                    FStar_Syntax_Syntax.default_sigmeta;
                                                  FStar_Syntax_Syntax.sigattrs
                                                    = []
                                                }]) [] axioms in
                                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                                  "haseq";
                                ses))))))
let (unoptimized_haseq_data :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun usubst ->
    fun bs ->
      fun haseq_ind ->
        fun mutuals ->
          fun acc ->
            fun data ->
              let rec is_mutual t =
                let uu____5664 =
                  let uu____5665 = FStar_Syntax_Subst.compress t in
                  uu____5665.FStar_Syntax_Syntax.n in
                match uu____5664 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5673) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5710 = is_mutual t' in
                    if uu____5710
                    then true
                    else
                      (let uu____5717 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5717)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5737) ->
                    is_mutual t'
                | uu____5742 -> false
              and exists_mutual uu___1_5744 =
                match uu___1_5744 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5765 =
                let uu____5766 = FStar_Syntax_Subst.compress dt1 in
                uu____5766.FStar_Syntax_Syntax.n in
              match uu____5765 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5772) ->
                  let dbs1 =
                    let uu____5802 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5802 in
                  let dbs2 =
                    let uu____5852 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5852 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5872 =
                               let uu____5877 =
                                 let uu____5878 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____5878] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5877 in
                             uu____5872 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5908 = is_mutual sort in
                             if uu____5908
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5921 =
                             let uu____5926 =
                               let uu____5927 =
                                 let uu____5936 =
                                   let uu____5937 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5937 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____5936 in
                               [uu____5927] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5926 in
                           uu____5921 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5984 -> acc
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle ->
    fun mutuals ->
      fun usubst ->
        fun us ->
          fun acc ->
            fun ty ->
              let uu____6034 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____6056, bs, t, uu____6059, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6071 -> failwith "Impossible!" in
              match uu____6034 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____6095 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____6095 t in
                  let uu____6104 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____6104 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____6114 =
                           let uu____6115 = FStar_Syntax_Subst.compress t2 in
                           uu____6115.FStar_Syntax_Syntax.n in
                         match uu____6114 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____6119) ->
                             ibs
                         | uu____6140 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____6149 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____6150 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6149
                           uu____6150 in
                       let ind1 =
                         let uu____6156 =
                           let uu____6161 =
                             FStar_List.map
                               (fun uu____6178 ->
                                  match uu____6178 with
                                  | (bv, aq) ->
                                      let uu____6197 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6197, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6161 in
                         uu____6156 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____6203 =
                           let uu____6208 =
                             FStar_List.map
                               (fun uu____6225 ->
                                  match uu____6225 with
                                  | (bv, aq) ->
                                      let uu____6244 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6244, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6208 in
                         uu____6203 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____6250 =
                           let uu____6255 =
                             let uu____6256 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____6256] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6255 in
                         uu____6250 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6293, uu____6294, uu____6295, t_lid,
                                   uu____6297, uu____6298)
                                  -> t_lid = lid
                              | uu____6305 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___867_6317 = fml in
                         let uu____6318 =
                           let uu____6319 =
                             let uu____6326 =
                               let uu____6327 =
                                 let uu____6348 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu____6353 =
                                   let uu____6366 =
                                     let uu____6377 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu____6377] in
                                   [uu____6366] in
                                 (uu____6348, uu____6353) in
                               FStar_Syntax_Syntax.Meta_pattern uu____6327 in
                             (fml, uu____6326) in
                           FStar_Syntax_Syntax.Tm_meta uu____6319 in
                         {
                           FStar_Syntax_Syntax.n = uu____6318;
                           FStar_Syntax_Syntax.pos =
                             (uu___867_6317.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___867_6317.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6446 =
                                  let uu____6451 =
                                    let uu____6452 =
                                      let uu____6461 =
                                        let uu____6462 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6462
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6461 in
                                    [uu____6452] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6451 in
                                uu____6446 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6515 =
                                  let uu____6520 =
                                    let uu____6521 =
                                      let uu____6530 =
                                        let uu____6531 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6531
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6530 in
                                    [uu____6521] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6520 in
                                uu____6515 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2 in
                       FStar_Syntax_Util.mk_conj acc fml3)
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          let mutuals =
            FStar_List.map
              (fun ty ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu____6623, uu____6624, uu____6625, uu____6626,
                      uu____6627)
                     -> lid
                 | uu____6636 -> failwith "Impossible!") tcs in
          let uu____6638 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6650, uu____6651, uu____6652, uu____6653) ->
                (lid, us)
            | uu____6662 -> failwith "Impossible!" in
          match uu____6638 with
          | (lid, us) ->
              let uu____6672 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6672 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6699 =
                       let uu____6700 =
                         let uu____6707 = get_haseq_axiom_lid lid in
                         (uu____6707, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6700 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6699;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = []
                     } in
                   [se])
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let uu____6761 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6786 ->
                    match uu___2_6786 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6788;
                        FStar_Syntax_Syntax.sigrng = uu____6789;
                        FStar_Syntax_Syntax.sigquals = uu____6790;
                        FStar_Syntax_Syntax.sigmeta = uu____6791;
                        FStar_Syntax_Syntax.sigattrs = uu____6792;_} -> true
                    | uu____6814 -> false)) in
          match uu____6761 with
          | (tys, datas) ->
              ((let uu____6837 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6848 ->
                          match uu___3_6848 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6850;
                              FStar_Syntax_Syntax.sigrng = uu____6851;
                              FStar_Syntax_Syntax.sigquals = uu____6852;
                              FStar_Syntax_Syntax.sigmeta = uu____6853;
                              FStar_Syntax_Syntax.sigattrs = uu____6854;_} ->
                              false
                          | uu____6875 -> true)) in
                if uu____6837
                then
                  let uu____6878 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6878
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6893 =
                       let uu____6894 = FStar_List.hd tys in
                       uu____6894.FStar_Syntax_Syntax.sigel in
                     match uu____6893 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6897, uvs, uu____6899, uu____6900,
                          uu____6901, uu____6902)
                         -> uvs
                     | uu____6911 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6916 =
                  FStar_List.fold_right
                    (fun tc ->
                       fun uu____6955 ->
                         match uu____6955 with
                         | (env1, all_tcs, g) ->
                             let uu____6995 = tc_tycon env1 tc in
                             (match uu____6995 with
                              | (env2, tc1, tc_u, guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____7022 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____7022
                                    then
                                      let uu____7025 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7025
                                    else ());
                                   (let uu____7030 =
                                      let uu____7031 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7031 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7030))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard) in
                match uu____6916 with
                | (env1, tcs, g) ->
                    let uu____7077 =
                      FStar_List.fold_right
                        (fun se ->
                           fun uu____7099 ->
                             match uu____7099 with
                             | (datas1, g1) ->
                                 let uu____7118 =
                                   let uu____7123 = tc_data env1 tcs in
                                   uu____7123 se in
                                 (match uu____7118 with
                                  | (data, g') ->
                                      let uu____7140 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____7140))) datas
                        ([], g) in
                    (match uu____7077 with
                     | (datas1, g1) ->
                         let uu____7161 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             let uu___976_7178 = g1 in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___976_7178.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___976_7178.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Env.univ_ineqs));
                               FStar_TypeChecker_Env.implicits =
                                 (uu___976_7178.FStar_TypeChecker_Env.implicits)
                             } in
                           (let uu____7188 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu____7188
                            then
                              let uu____7193 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7193
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if
                             (FStar_List.length univs1) =
                               (Prims.parse_int "0")
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7212 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs in
                              (uu____7212, datas1)) in
                         (match uu____7161 with
                          | (tcs1, datas2) ->
                              let sig_bndle =
                                let uu____7244 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____7245 =
                                  FStar_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7244;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7245
                                } in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l, univs2, binders, typ,
                                            uu____7271, uu____7272)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7292 =
                                               let uu____7298 =
                                                 let uu____7300 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu____7302 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7300 uu____7302 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7298) in
                                             FStar_Errors.raise_error
                                               uu____7292
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu____7306 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____7306 with
                                            | FStar_Pervasives_Native.None ->
                                                ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1, uu____7322)
                                                ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7353 ->
                                                        let uu____7354 =
                                                          let uu____7361 =
                                                            let uu____7362 =
                                                              let uu____7377
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ in
                                                              (binders,
                                                                uu____7377) in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____7362 in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____7361 in
                                                        uu____7354
                                                          FStar_Pervasives_Native.None
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs2, body) in
                                                if
                                                  (FStar_List.length univs2)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ1))
                                                then
                                                  let uu____7399 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____7399 with
                                                   | (uu____7404, inferred)
                                                       ->
                                                       let uu____7406 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1 in
                                                       (match uu____7406 with
                                                        | (uu____7411,
                                                           expected) ->
                                                            let uu____7413 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected in
                                                            if uu____7413
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7420 -> ()));
                               (sig_bndle, tcs1, datas2))))))
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"]
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun fvq ->
      fun refine_domain ->
        fun env ->
          fun tc ->
            fun lid ->
              fun uvs ->
                fun inductive_tps ->
                  fun indices ->
                    fun fields ->
                      let p = FStar_Ident.range_of_lid lid in
                      let pos q = FStar_Syntax_Syntax.withinfo q p in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          let uu____7531 =
                            let uu____7538 =
                              let uu____7539 =
                                let uu____7546 =
                                  let uu____7549 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7549 in
                                (uu____7546, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7539 in
                            FStar_Syntax_Syntax.mk uu____7538 in
                          uu____7531 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7583 ->
                                  match uu____7583 with
                                  | (x, imp) ->
                                      let uu____7602 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7602, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7606 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7606 in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ in
                           let sort =
                             let disc_fvar =
                               let uu____7629 =
                                 FStar_Ident.set_lid_range disc_name p in
                               FStar_Syntax_Syntax.fvar uu____7629
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None in
                             let uu____7631 =
                               let uu____7634 =
                                 let uu____7637 =
                                   let uu____7642 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7643 =
                                     let uu____7644 =
                                       let uu____7653 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7653 in
                                     [uu____7644] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7642
                                     uu____7643 in
                                 uu____7637 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7634 in
                             FStar_Syntax_Util.refine x uu____7631 in
                           let uu____7678 =
                             let uu___1049_7679 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1049_7679.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1049_7679.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7678) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7696 =
                          FStar_List.map
                            (fun uu____7720 ->
                               match uu____7720 with
                               | (x, uu____7734) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7696 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7793 ->
                                match uu____7793 with
                                | (x, uu____7807) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))) in
                      let early_prims_inductive =
                        (let uu____7818 =
                           FStar_TypeChecker_Env.current_module env in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7818)
                          &&
                          (FStar_List.existsb
                             (fun s ->
                                s = (tc.FStar_Ident.ident).FStar_Ident.idText)
                             early_prims_inductives) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             early_prims_inductive ||
                               (let uu____7839 =
                                  let uu____7841 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7841.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7839) in
                           let quals =
                             let uu____7845 =
                               FStar_List.filter
                                 (fun uu___4_7849 ->
                                    match uu___4_7849 with
                                    | FStar_Syntax_Syntax.Abstract ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                        -> true
                                    | FStar_Syntax_Syntax.NoExtract -> true
                                    | FStar_Syntax_Syntax.Private -> true
                                    | uu____7854 -> false) iquals in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7845 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7892 =
                                 let uu____7893 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7893 in
                               FStar_Syntax_Syntax.mk_Total uu____7892 in
                             let uu____7894 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7894 in
                           let decl =
                             let uu____7898 =
                               FStar_Ident.range_of_lid discriminator_name in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7898;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             } in
                           (let uu____7900 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7900
                            then
                              let uu____7904 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7904
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Util.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j ->
                                             fun uu____7965 ->
                                               match uu____7965 with
                                               | (x, imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7990 =
                                                       let uu____7993 =
                                                         let uu____7994 =
                                                           let uu____8001 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____8001,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7994 in
                                                       pos uu____7993 in
                                                     (uu____7990, b)
                                                   else
                                                     (let uu____8009 =
                                                        let uu____8012 =
                                                          let uu____8013 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8013 in
                                                        pos uu____8012 in
                                                      (uu____8009, b)))) in
                                   let pat_true =
                                     let uu____8032 =
                                       let uu____8035 =
                                         let uu____8036 =
                                           let uu____8050 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____8050, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8036 in
                                       pos uu____8035 in
                                     (uu____8032,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____8085 =
                                       let uu____8088 =
                                         let uu____8089 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8089 in
                                       pos uu____8088 in
                                     (uu____8085,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____8103 =
                                     let uu____8110 =
                                       let uu____8111 =
                                         let uu____8134 =
                                           let uu____8151 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8166 =
                                             let uu____8183 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8183] in
                                           uu____8151 :: uu____8166 in
                                         (arg_exp, uu____8134) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8111 in
                                     FStar_Syntax_Syntax.mk uu____8110 in
                                   uu____8103 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____8259 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8259
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                       (Prims.parse_int "1"))
                                else
                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1") in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun in
                              let lb =
                                let uu____8281 =
                                  let uu____8286 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____8286 in
                                let uu____8287 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                FStar_Syntax_Util.mk_letbinding uu____8281
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8287 [] FStar_Range.dummyRange in
                              let impl =
                                let uu____8293 =
                                  let uu____8294 =
                                    let uu____8301 =
                                      let uu____8304 =
                                        let uu____8305 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8305
                                          (fun fv ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8304] in
                                    ((false, [lb]), uu____8301) in
                                  FStar_Syntax_Syntax.Sig_let uu____8294 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8293;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____8319 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8319
                               then
                                 let uu____8323 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8323
                               else ());
                              [decl; impl])) in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder) in
                      let binders =
                        FStar_List.append imp_binders [arg_binder] in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____8396 ->
                                  match uu____8396 with
                                  | (a, uu____8405) ->
                                      let uu____8410 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8410 with
                                       | (field_name, uu____8416) ->
                                           let field_proj_tm =
                                             let uu____8418 =
                                               let uu____8419 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8419 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8418 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8445 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____8487 ->
                                    match uu____8487 with
                                    | (x, uu____8498) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8504 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8504 with
                                         | (field_name, uu____8512) ->
                                             let t =
                                               let uu____8516 =
                                                 let uu____8517 =
                                                   let uu____8520 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8520 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8517 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8516 in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8526 =
                                                    let uu____8528 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8528.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8526) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8547 =
                                                   FStar_List.filter
                                                     (fun uu___5_8551 ->
                                                        match uu___5_8551
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                            -> false
                                                        | uu____8554 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8547
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___6_8569 ->
                                                         match uu___6_8569
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                             -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                             -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                             -> true
                                                         | FStar_Syntax_Syntax.Private
                                                             -> true
                                                         | uu____8575 ->
                                                             false)) in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1) in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute] in
                                             let decl =
                                               let uu____8586 =
                                                 FStar_Ident.range_of_lid
                                                   field_name in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8586;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               } in
                                             ((let uu____8588 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8588
                                               then
                                                 let uu____8592 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8592
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j ->
                                                           fun uu____8646 ->
                                                             match uu____8646
                                                             with
                                                             | (x1, imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8672
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8672,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8688
                                                                    =
                                                                    let uu____8691
                                                                    =
                                                                    let uu____8692
                                                                    =
                                                                    let uu____8699
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8699,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8692 in
                                                                    pos
                                                                    uu____8691 in
                                                                    (uu____8688,
                                                                    b))
                                                                   else
                                                                    (let uu____8707
                                                                    =
                                                                    let uu____8710
                                                                    =
                                                                    let uu____8711
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8711 in
                                                                    pos
                                                                    uu____8710 in
                                                                    (uu____8707,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8730 =
                                                     let uu____8733 =
                                                       let uu____8734 =
                                                         let uu____8748 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8748,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8734 in
                                                     pos uu____8733 in
                                                   let uu____8758 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8730,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8758) in
                                                 let body =
                                                   let uu____8774 =
                                                     let uu____8781 =
                                                       let uu____8782 =
                                                         let uu____8805 =
                                                           let uu____8822 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8822] in
                                                         (arg_exp,
                                                           uu____8805) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8782 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8781 in
                                                   uu____8774
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8887 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8887
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       (FStar_Syntax_Syntax.Delta_equational_at_level
                                                          (Prims.parse_int "1"))
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational_at_level
                                                       (Prims.parse_int "1") in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun in
                                                 let lb =
                                                   let uu____8906 =
                                                     let uu____8911 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8911 in
                                                   let uu____8912 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8906;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8912;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   } in
                                                 let impl =
                                                   let uu____8918 =
                                                     let uu____8919 =
                                                       let uu____8926 =
                                                         let uu____8929 =
                                                           let uu____8930 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8930
                                                             (fun fv ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8929] in
                                                       ((false, [lb]),
                                                         uu____8926) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8919 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8918;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   } in
                                                 (let uu____8944 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8944
                                                  then
                                                    let uu____8948 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8948
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8445 FStar_List.flatten in
                      FStar_List.append discriminator_ses projectors_ses
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun env ->
      fun tcs ->
        fun se ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid, uvs, t, typ_lid, n_typars, uu____9002) when
              let uu____9009 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid in
              Prims.op_Negation uu____9009 ->
              let uu____9011 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____9011 with
               | (univ_opening, uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____9033 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____9033 with
                    | (formals, uu____9051) ->
                        let uu____9072 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1 ->
                                 let uu____9107 =
                                   let uu____9109 =
                                     let uu____9110 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____9110 in
                                   FStar_Ident.lid_equals typ_lid uu____9109 in
                                 if uu____9107
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9132, uvs', tps, typ0,
                                        uu____9136, constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9156 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None ->
                              let uu____9205 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid in
                              if uu____9205
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng in
                        (match uu____9072 with
                         | (inductive_tps, typ0, should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____9243 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____9243 with
                              | (indices, uu____9261) ->
                                  let refine_domain =
                                    let uu____9284 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9291 ->
                                              match uu___7_9291 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9293 -> true
                                              | uu____9303 -> false)) in
                                    if uu____9284
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___8_9318 =
                                      match uu___8_9318 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9321, fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9333 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____9334 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____9334 with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q in
                                  let iquals1 =
                                    if
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract iquals)
                                        &&
                                        (Prims.op_Negation
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Private
                                              iquals))
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals in
                                  let fields =
                                    let uu____9347 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____9347 with
                                    | (imp_tps, fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9430 ->
                                               fun uu____9431 ->
                                                 match (uu____9430,
                                                         uu____9431)
                                                 with
                                                 | ((x, uu____9457),
                                                    (x', uu____9459)) ->
                                                     let uu____9480 =
                                                       let uu____9487 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____9487) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9480) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9492 -> []