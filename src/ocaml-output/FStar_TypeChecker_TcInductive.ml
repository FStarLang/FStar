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
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc, uvs, tps, k, mutuals, data) ->
          let env0 = env in
          let uu____49 = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu____49 with
           | (usubst, uvs1) ->
               let uu____76 =
                 let uu____83 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu____84 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu____85 =
                   let uu____86 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst in
                   FStar_Syntax_Subst.subst uu____86 k in
                 (uu____83, uu____84, uu____85) in
               (match uu____76 with
                | (env1, tps1, k1) ->
                    let uu____106 = FStar_Syntax_Subst.open_term tps1 k1 in
                    (match uu____106 with
                     | (tps2, k2) ->
                         let uu____121 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2 in
                         (match uu____121 with
                          | (tps3, env_tps, guard_params, us) ->
                              let uu____142 =
                                let uu____161 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2 in
                                match uu____161 with
                                | (k3, uu____187, g) ->
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
                                    let uu____190 =
                                      FStar_Syntax_Util.arrow_formals k4 in
                                    let uu____205 =
                                      let uu____206 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____206 in
                                    (uu____190, uu____205) in
                              (match uu____142 with
                               | ((indices, t), guard) ->
                                   let k3 =
                                     let uu____269 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow indices
                                       uu____269 in
                                   let uu____272 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____272 with
                                    | (t_type, u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____289 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq) in
                                              Prims.op_Negation uu____289))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type) in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____293 =
                                              let uu____298 =
                                                let uu____299 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                let uu____300 =
                                                  FStar_Ident.string_of_lid
                                                    tc in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____299 uu____300 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____298) in
                                            FStar_Errors.raise_error
                                              uu____293
                                              s.FStar_Syntax_Syntax.sigrng)
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1 in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 false tps3 guard in
                                          let t_tc =
                                            let uu____309 =
                                              let uu____318 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1) in
                                              let uu____335 =
                                                let uu____344 =
                                                  let uu____357 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1 in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____357 in
                                                FStar_All.pipe_right indices
                                                  uu____344 in
                                              FStar_List.append uu____318
                                                uu____335 in
                                            let uu____380 =
                                              let uu____383 =
                                                let uu____384 =
                                                  let uu____389 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1 in
                                                  FStar_Syntax_Subst.subst
                                                    uu____389 in
                                                FStar_All.pipe_right t
                                                  uu____384 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____383 in
                                            FStar_Syntax_Util.arrow uu____309
                                              uu____380 in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3 in
                                          let uu____406 =
                                            let uu____411 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4 in
                                            let uu____412 =
                                              let uu____413 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1 in
                                              FStar_Syntax_Subst.subst
                                                uu____413 k4 in
                                            (uu____411, uu____412) in
                                          match uu____406 with
                                          | (tps5, k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None in
                                              let uu____433 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs1 t_tc in
                                              (match uu____433 with
                                               | (uvs2, t_tc1) ->
                                                   let uu____448 =
                                                     FStar_TypeChecker_Env.push_let_binding
                                                       env0
                                                       (FStar_Util.Inr fv_tc)
                                                       (uvs2, t_tc1) in
                                                   (uu____448,
                                                     (let uu___63_454 = s in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_inductive_typ
                                                             (tc, uvs2, tps5,
                                                               k5, mutuals,
                                                               data));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___63_454.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___63_454.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___63_454.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___63_454.FStar_Syntax_Syntax.sigattrs);
                                                        FStar_Syntax_Syntax.sigopts
                                                          =
                                                          (uu___63_454.FStar_Syntax_Syntax.sigopts)
                                                      }), u, guard1))))))))))
      | uu____459 -> failwith "impossible"
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Common.guard_t))
  =
  fun env ->
    fun tcs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (c, _uvs, t, tc_lid, ntps, _mutual_tcs) ->
            let uu____519 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu____519 with
             | (usubst, _uvs1) ->
                 let uu____542 =
                   let uu____547 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu____548 = FStar_Syntax_Subst.subst usubst t in
                   (uu____547, uu____548) in
                 (match uu____542 with
                  | (env1, t1) ->
                      let uu____555 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____594 ->
                               match uu____594 with
                               | (se1, u_tc) ->
                                   let uu____609 =
                                     let uu____610 =
                                       let uu____611 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____611 in
                                     FStar_Ident.lid_equals tc_lid uu____610 in
                                   if uu____609
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____630, uu____631, tps,
                                           uu____633, uu____634, uu____635)
                                          ->
                                          let tps1 =
                                            let uu____645 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu____645
                                              (FStar_List.map
                                                 (fun uu____685 ->
                                                    match uu____685 with
                                                    | (x, uu____699) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag)))) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu____707 =
                                            let uu____714 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu____714, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu____707
                                      | uu____721 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu____762 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu____762
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu____555 with
                       | (env2, tps, u_tc) ->
                           let uu____789 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu____797 =
                               let uu____798 = FStar_Syntax_Subst.compress t2 in
                               uu____798.FStar_Syntax_Syntax.n in
                             match uu____797 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu____829 = FStar_Util.first_N ntps bs in
                                 (match uu____829 with
                                  | (uu____862, bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          t2.FStar_Syntax_Syntax.pos in
                                      let subst =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i ->
                                                fun uu____933 ->
                                                  match uu____933 with
                                                  | (x, uu____941) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            (Prims.int_one +
                                                               i)), x))) in
                                      let uu____946 =
                                        let uu____951 =
                                          FStar_Syntax_Subst.subst subst t3 in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu____951 in
                                      (match uu____946 with
                                       | (bs1, c1) ->
                                           let uu____960 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1) in
                                           if uu____960
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu____970 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1) in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu____970)))
                             | uu____977 -> ([], t2) in
                           (match uu____789 with
                            | (arguments, result) ->
                                ((let uu____997 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu____997
                                  then
                                    let uu____998 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu____999 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu____1000 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____998 uu____999 uu____1000
                                  else ());
                                 (let uu____1002 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu____1002 with
                                  | (arguments1, env', us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          result.FStar_Syntax_Syntax.pos in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc in
                                      let uu____1020 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result in
                                      (match uu____1020 with
                                       | (result1, res_lcomp) ->
                                           let uu____1031 =
                                             FStar_Syntax_Util.head_and_args'
                                               result1 in
                                           (match uu____1031 with
                                            | (head, args) ->
                                                let p_args =
                                                  let uu____1083 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1083 in
                                                (FStar_List.iter2
                                                   (fun uu____1165 ->
                                                      fun uu____1166 ->
                                                        match (uu____1165,
                                                                uu____1166)
                                                        with
                                                        | ((bv, uu____1196),
                                                           (t2, uu____1198))
                                                            ->
                                                            let uu____1225 =
                                                              let uu____1226
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2 in
                                                              uu____1226.FStar_Syntax_Syntax.n in
                                                            (match uu____1225
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1230 ->
                                                                 let uu____1231
                                                                   =
                                                                   let uu____1236
                                                                    =
                                                                    let uu____1237
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu____1238
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1237
                                                                    uu____1238 in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1236) in
                                                                 FStar_Errors.raise_error
                                                                   uu____1231
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1240 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                    FStar_All.pipe_right
                                                      uu____1240
                                                      FStar_Syntax_Util.unrefine in
                                                  (let uu____1242 =
                                                     let uu____1243 =
                                                       FStar_Syntax_Subst.compress
                                                         ty in
                                                     uu____1243.FStar_Syntax_Syntax.n in
                                                   match uu____1242 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1246 -> ()
                                                   | uu____1247 ->
                                                       let uu____1248 =
                                                         let uu____1253 =
                                                           let uu____1254 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1 in
                                                           let uu____1255 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1254
                                                             uu____1255 in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1253) in
                                                       FStar_Errors.raise_error
                                                         uu____1248
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1257 =
                                                       let uu____1258 =
                                                         FStar_Syntax_Subst.compress
                                                           head in
                                                       uu____1258.FStar_Syntax_Syntax.n in
                                                     match uu____1257 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1262;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1263;_},
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
                                                                    let uu____1276
                                                                    =
                                                                    let uu____1277
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Range.dummyRange in
                                                                    let uu____1278
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____1277
                                                                    uu____1278 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1276)
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
                                                     | uu____1281 ->
                                                         let uu____1282 =
                                                           let uu____1287 =
                                                             let uu____1288 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid in
                                                             let uu____1289 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1288
                                                               uu____1289 in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1287) in
                                                         FStar_Errors.raise_error
                                                           uu____1282
                                                           se.FStar_Syntax_Syntax.sigrng in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g ->
                                                          fun uu____1304 ->
                                                            fun u_x ->
                                                              match uu____1304
                                                              with
                                                              | (x,
                                                                 uu____1313)
                                                                  ->
                                                                  let uu____1318
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1318)
                                                       g_uvs arguments1 us in
                                                   let t2 =
                                                     let uu____1322 =
                                                       let uu____1331 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1371
                                                                 ->
                                                                 match uu____1371
                                                                 with
                                                                 | (x,
                                                                    uu____1385)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                       FStar_List.append
                                                         uu____1331
                                                         arguments1 in
                                                     let uu____1398 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1 in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1322 uu____1398 in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2 in
                                                   ((let uu___189_1403 = se in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___189_1403.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___189_1403.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___189_1403.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___189_1403.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___189_1403.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1406 -> failwith "impossible"
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
               (fun uu____1495 ->
                  match uu____1495 with
                  | (se, uu____1501) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1502, uu____1503, tps, k, uu____1506,
                            uu____1507)
                           ->
                           let uu____1516 =
                             let uu____1517 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1517 in
                           FStar_Syntax_Syntax.null_binder uu____1516
                       | uu____1522 -> failwith "Impossible"))) in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1550, uu____1551, t, uu____1553, uu____1554,
                       uu____1555)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1560 -> failwith "Impossible")) in
        let t =
          let uu____1564 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1564 in
        (let uu____1574 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu____1574
         then
           let uu____1575 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1575
         else ());
        (let uu____1577 =
           FStar_TypeChecker_Generalize.generalize_universes env t in
         match uu____1577 with
         | (uvs, t1) ->
             ((let uu____1597 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu____1597
               then
                 let uu____1598 =
                   let uu____1599 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u -> FStar_Ident.string_of_id u)) in
                   FStar_All.pipe_right uu____1599 (FStar_String.concat ", ") in
                 let uu____1610 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1598 uu____1610
               else ());
              (let uu____1612 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu____1612 with
               | (uvs1, t2) ->
                   let uu____1627 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu____1627 with
                    | (args, uu____1643) ->
                        let uu____1648 =
                          FStar_Util.first_N (FStar_List.length binders) args in
                        (match uu____1648 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1753 ->
                                    fun uu____1754 ->
                                      match (uu____1753, uu____1754) with
                                      | ((x, uu____1776), (se, uu____1778))
                                          ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu____1794, tps,
                                                uu____1796, mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu____1808 =
                                                 let uu____1813 =
                                                   let uu____1814 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu____1814.FStar_Syntax_Syntax.n in
                                                 match uu____1813 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu____1843 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1 in
                                                     (match uu____1843 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____1921 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu____1940 -> ([], ty) in
                                               (match uu____1808 with
                                                | (tps1, t3) ->
                                                    let uu___266_1949 = se in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___266_1949.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___266_1949.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___266_1949.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___266_1949.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___266_1949.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____1954 ->
                                               failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____1960 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun uu____1964 ->
                                             FStar_Syntax_Syntax.U_name
                                               uu____1964)) in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_1984 ->
                                             match uu___0_1984 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu____1990,
                                                    uu____1991, uu____1992,
                                                    uu____1993, uu____1994);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____1995;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____1996;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____1997;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____1998;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____1999;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2014 ->
                                                 failwith "Impossible")) in
                                   FStar_List.map2
                                     (fun uu____2037 ->
                                        fun d ->
                                          match uu____2037 with
                                          | (t3, uu____2046) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu____2052,
                                                    uu____2053, tc, ntps,
                                                    mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2062 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_All.pipe_right
                                                       uu____2062
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   let uu___303_2063 = d in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___303_2063.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___303_2063.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___303_2063.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___303_2063.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___303_2063.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2066 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env ->
    fun msg ->
      let uu____2086 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____2086
      then
        let uu____2087 =
          let uu____2088 =
            let uu____2089 = msg () in Prims.op_Hat uu____2089 "\n" in
          Prims.op_Hat "Positivity::" uu____2088 in
        FStar_Util.print_string uu____2087
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____2101 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____2101
let rec (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____2121 =
      let uu____2122 = FStar_Syntax_Subst.compress t in
      uu____2122.FStar_Syntax_Syntax.n in
    match uu____2121 with
    | FStar_Syntax_Syntax.Tm_name uu____2131 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives_Native.Some (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu____2147 =
          let uu____2148 = FStar_Syntax_Subst.compress t1 in
          uu____2148.FStar_Syntax_Syntax.n in
        (match uu____2147 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, us)
         | uu____2162 ->
             failwith
               "try_get_fv: Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2170, uu____2171) ->
        try_get_fv t1
    | uu____2212 ->
        let uu____2213 =
          let uu____2214 = FStar_Syntax_Print.tag_of_term t in
          Prims.op_Hat "try_get_fv: did not expect t to be a : " uu____2214 in
        failwith uu____2213
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
          let uu____2249 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2285 ->
               match uu____2285 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2328 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2328 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2249
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          debug_log env
            (fun uu____2524 ->
               let uu____2525 = FStar_Syntax_Print.term_to_string btype in
               Prims.op_Hat "Checking strict positivity in type: " uu____2525);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.ForExtraction;
               FStar_TypeChecker_Env.Unascribe;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype in
           debug_log env
             (fun uu____2530 ->
                let uu____2531 = FStar_Syntax_Print.term_to_string btype1 in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2531);
           (let uu____2534 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2534) ||
             ((debug_log env
                 (fun uu____2543 ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2544 =
                  let uu____2545 = FStar_Syntax_Subst.compress btype1 in
                  uu____2545.FStar_Syntax_Syntax.n in
                match uu____2544 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let fv_us_opt = try_get_fv t in
                    let uu____2581 =
                      FStar_All.pipe_right fv_us_opt FStar_Util.is_none in
                    if uu____2581
                    then true
                    else
                      (let uu____2593 =
                         FStar_All.pipe_right fv_us_opt FStar_Util.must in
                       match uu____2593 with
                       | (fv, us) ->
                           let uu____2614 =
                             FStar_Ident.lid_equals
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               ty_lid in
                           if uu____2614
                           then
                             (debug_log env
                                (fun uu____2617 ->
                                   "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                              FStar_List.for_all
                                (fun uu____2628 ->
                                   match uu____2628 with
                                   | (t1, uu____2636) ->
                                       let uu____2641 =
                                         ty_occurs_in ty_lid t1 in
                                       Prims.op_Negation uu____2641) args)
                           else
                             (debug_log env
                                (fun uu____2645 ->
                                   "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                              ty_nested_positive_in_inductive ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env
                       (fun uu____2670 ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp =
                        let c1 =
                          let uu____2675 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu____2675
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2679 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu____2679
                             (FStar_List.existsb
                                (fun q -> q = FStar_Syntax_Syntax.TotalEffect))) in
                      if Prims.op_Negation check_comp
                      then
                        (debug_log env
                           (fun uu____2688 ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2692 ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2703 ->
                               match uu____2703 with
                               | (b, uu____2711) ->
                                   let uu____2716 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2716) sbs)
                           &&
                           ((let uu____2721 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2721 with
                             | (uu____2726, return_type) ->
                                 let uu____2728 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2728)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2729 ->
                    (debug_log env
                       (fun uu____2732 ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2733 ->
                    (debug_log env
                       (fun uu____2736 ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2738) ->
                    (debug_log env
                       (fun uu____2745 ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2747) ->
                    (debug_log env
                       (fun uu____2754 ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2755, branches) ->
                    (debug_log env
                       (fun uu____2795 ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2815 ->
                          match uu____2815 with
                          | (p, uu____2827, t) ->
                              let bs =
                                let uu____2846 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2846 in
                              let uu____2855 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2855 with
                               | (bs1, t1) ->
                                   let uu____2862 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2862)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2864, uu____2865)
                    ->
                    (debug_log env
                       (fun uu____2908 ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2909 ->
                    (debug_log env
                       (fun uu____2913 ->
                          let uu____2914 =
                            let uu____2915 =
                              FStar_Syntax_Print.tag_of_term btype1 in
                            let uu____2916 =
                              let uu____2917 =
                                FStar_Syntax_Print.term_to_string btype1 in
                              Prims.op_Hat " and term: " uu____2917 in
                            Prims.op_Hat uu____2915 uu____2916 in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____2914);
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
              debug_log env
                (fun uu____2927 ->
                   let uu____2928 =
                     let uu____2929 = FStar_Ident.string_of_lid ilid in
                     let uu____2930 =
                       let uu____2931 =
                         FStar_Syntax_Print.args_to_string args in
                       Prims.op_Hat " applied to arguments: " uu____2931 in
                     Prims.op_Hat uu____2929 uu____2930 in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____2928);
              (let uu____2932 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2932 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2945 =
                       let uu____2946 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       FStar_TypeChecker_Env.fv_has_attr env uu____2946
                         FStar_Parser_Const.assume_strictly_positive_attr_lid in
                     (if uu____2945
                      then
                        (debug_log env
                           (fun uu____2950 ->
                              let uu____2951 = FStar_Ident.string_of_lid ilid in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____2951);
                         true)
                      else
                        (debug_log env
                           (fun uu____2955 ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____2957 =
                        already_unfolded ilid args unfolded env in
                      if uu____2957
                      then
                        (debug_log env
                           (fun uu____2960 ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____2963 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu____2963 in
                         debug_log env
                           (fun uu____2969 ->
                              let uu____2970 =
                                let uu____2971 =
                                  FStar_Util.string_of_int num_ibs in
                                Prims.op_Hat uu____2971
                                  ", also adding to the memo table" in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____2970);
                         (let uu____2973 =
                            let uu____2974 = FStar_ST.op_Bang unfolded in
                            let uu____2987 =
                              let uu____2994 =
                                let uu____2999 =
                                  let uu____3000 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3000 in
                                (ilid, uu____2999) in
                              [uu____2994] in
                            FStar_List.append uu____2974 uu____2987 in
                          FStar_ST.op_Colon_Equals unfolded uu____2973);
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
                    (fun uu____3084 ->
                       let uu____3085 =
                         let uu____3086 = FStar_Ident.string_of_lid dlid in
                         let uu____3087 =
                           let uu____3088 = FStar_Ident.string_of_lid ilid in
                           Prims.op_Hat " of the inductive " uu____3088 in
                         Prims.op_Hat uu____3086 uu____3087 in
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         uu____3085);
                  (let uu____3089 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3089 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3113 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        debug_log env
                          (fun uu____3117 ->
                             let uu____3118 =
                               FStar_Syntax_Print.term_to_string dt in
                             Prims.op_Hat
                               "Checking nested positivity in the data constructor type: "
                               uu____3118);
                        (let uu____3119 =
                           let uu____3120 = FStar_Syntax_Subst.compress dt in
                           uu____3120.FStar_Syntax_Syntax.n in
                         match uu____3119 with
                         | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                             (debug_log env
                                (fun uu____3147 ->
                                   "Checked nested positivity in Tm_arrow data constructor type");
                              (let uu____3148 =
                                 FStar_List.splitAt num_ibs dbs in
                               match uu____3148 with
                               | (ibs, dbs1) ->
                                   let ibs1 =
                                     FStar_Syntax_Subst.open_binders ibs in
                                   let dbs2 =
                                     let uu____3211 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_binders
                                       uu____3211 dbs1 in
                                   let c1 =
                                     let uu____3215 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_comp uu____3215
                                       c in
                                   let uu____3218 =
                                     FStar_List.splitAt num_ibs args in
                                   (match uu____3218 with
                                    | (args1, uu____3252) ->
                                        let subst =
                                          FStar_List.fold_left2
                                            (fun subst ->
                                               fun ib ->
                                                 fun arg ->
                                                   FStar_List.append subst
                                                     [FStar_Syntax_Syntax.NT
                                                        ((FStar_Pervasives_Native.fst
                                                            ib),
                                                          (FStar_Pervasives_Native.fst
                                                             arg))]) [] ibs1
                                            args1 in
                                        let dbs3 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst dbs2 in
                                        let c2 =
                                          let uu____3344 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length dbs3) subst in
                                          FStar_Syntax_Subst.subst_comp
                                            uu____3344 c1 in
                                        (debug_log env
                                           (fun uu____3356 ->
                                              let uu____3357 =
                                                let uu____3358 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    "; " dbs3 in
                                                let uu____3359 =
                                                  let uu____3360 =
                                                    FStar_Syntax_Print.comp_to_string
                                                      c2 in
                                                  Prims.op_Hat ", and c: "
                                                    uu____3360 in
                                                Prims.op_Hat uu____3358
                                                  uu____3359 in
                                              Prims.op_Hat
                                                "Checking nested positivity in the unfolded data constructor binders as: "
                                                uu____3357);
                                         ty_nested_positive_in_type ty_lid
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (dbs3, c2)) ilid num_ibs
                                           unfolded env))))
                         | uu____3371 ->
                             (debug_log env
                                (fun uu____3374 ->
                                   "Checking nested positivity in the data constructor type that is not an arrow");
                              (let uu____3375 =
                                 let uu____3376 =
                                   FStar_Syntax_Subst.compress dt in
                                 uu____3376.FStar_Syntax_Syntax.n in
                               ty_nested_positive_in_type ty_lid uu____3375
                                 ilid num_ibs unfolded env)))))
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
                     (fun uu____3413 ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3414 =
                      let uu____3419 = try_get_fv t1 in
                      FStar_All.pipe_right uu____3419 FStar_Util.must in
                    match uu____3414 with
                    | (fv, uu____3441) ->
                        let uu____3442 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____3442
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  (debug_log env
                     (fun uu____3469 ->
                        let uu____3470 =
                          FStar_Syntax_Print.binders_to_string "; " sbs in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3470);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3472 =
                      FStar_List.fold_left
                        (fun uu____3491 ->
                           fun b ->
                             match uu____3491 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3514 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3517 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3514, uu____3517))) (true, env)
                        sbs1 in
                    match uu____3472 with | (b, uu____3531) -> b))
              | uu____3532 ->
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
              let uu____3563 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3563 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3587 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3591 ->
                        let uu____3592 = FStar_Syntax_Print.term_to_string dt in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3592);
                   (let uu____3593 =
                      let uu____3594 = FStar_Syntax_Subst.compress dt in
                      uu____3594.FStar_Syntax_Syntax.n in
                    match uu____3593 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3597 ->
                        (debug_log env
                           (fun uu____3600 ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3602) ->
                        let dbs1 =
                          let uu____3632 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3632 in
                        let dbs2 =
                          let uu____3682 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3682 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        (debug_log env
                           (fun uu____3689 ->
                              let uu____3690 =
                                let uu____3691 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3) in
                                Prims.op_Hat uu____3691 " binders" in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3690);
                         (let uu____3698 =
                            FStar_List.fold_left
                              (fun uu____3717 ->
                                 fun b ->
                                   match uu____3717 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3740 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3743 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3740, uu____3743)))
                              (true, env) dbs3 in
                          match uu____3698 with | (b, uu____3757) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3758, uu____3759) ->
                        (debug_log env
                           (fun uu____3786 ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs) ->
                        (debug_log env
                           (fun uu____3795 ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3796 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3814 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____3830, uu____3831, uu____3832) ->
            (lid, us, bs)
        | uu____3841 -> failwith "Impossible!" in
      match uu____3814 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____3851 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3851 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3874 =
                 let uu____3877 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3877 in
               FStar_List.for_all
                 (fun d ->
                    let uu____3889 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3889
                      unfolded_inductives env2) uu____3874)
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
        (uu____3920, uu____3921, t, uu____3923, uu____3924, uu____3925) -> t
    | uu____3930 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = FStar_Ident.string_of_lid lid in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____3940 =
         let uu____3941 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____3941 haseq_suffix in
       uu____3940 = Prims.int_zero)
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____3947 =
      let uu____3948 = FStar_Ident.ns_of_lid lid in
      let uu____3951 =
        let uu____3954 =
          let uu____3955 =
            let uu____3956 =
              let uu____3957 = FStar_Ident.ident_of_lid lid in
              FStar_Ident.string_of_id uu____3957 in
            Prims.op_Hat uu____3956 haseq_suffix in
          FStar_Ident.id_of_text uu____3955 in
        [uu____3954] in
      FStar_List.append uu____3948 uu____3951 in
    FStar_Ident.lid_of_ids uu____3947
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
          let uu____4002 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4016, bs, t, uu____4019, uu____4020) ->
                (lid, bs, t)
            | uu____4029 -> failwith "Impossible!" in
          match uu____4002 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____4051 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____4051 t in
              let uu____4060 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____4060 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____4078 =
                       let uu____4079 = FStar_Syntax_Subst.compress t2 in
                       uu____4079.FStar_Syntax_Syntax.n in
                     match uu____4078 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4083) -> ibs
                     | uu____4104 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____4113 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____4114 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4113 uu____4114 in
                   let ind1 =
                     let uu____4118 =
                       FStar_List.map
                         (fun uu____4135 ->
                            match uu____4135 with
                            | (bv, aq) ->
                                let uu____4154 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4154, aq)) bs2 in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu____4118
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____4158 =
                       FStar_List.map
                         (fun uu____4175 ->
                            match uu____4175 with
                            | (bv, aq) ->
                                let uu____4194 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4194, aq)) ibs1 in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4158
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____4198 =
                       let uu____4199 = FStar_Syntax_Syntax.as_arg ind2 in
                       [uu____4199] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu____4198 FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____4248 =
                            let uu____4249 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____4249 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4248) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____4262 =
                              let uu____4265 =
                                let uu____4266 =
                                  let uu____4275 =
                                    FStar_Syntax_Syntax.bv_to_name
                                      (FStar_Pervasives_Native.fst b) in
                                  FStar_Syntax_Syntax.as_arg uu____4275 in
                                [uu____4266] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq uu____4265
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____4262)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___677_4298 = fml in
                     let uu____4299 =
                       let uu____4300 =
                         let uu____4307 =
                           let uu____4308 =
                             let uu____4329 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu____4334 =
                               let uu____4347 =
                                 let uu____4358 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____4358] in
                               [uu____4347] in
                             (uu____4329, uu____4334) in
                           FStar_Syntax_Syntax.Meta_pattern uu____4308 in
                         (fml, uu____4307) in
                       FStar_Syntax_Syntax.Tm_meta uu____4300 in
                     {
                       FStar_Syntax_Syntax.n = uu____4299;
                       FStar_Syntax_Syntax.pos =
                         (uu___677_4298.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___677_4298.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4427 =
                              let uu____4428 =
                                let uu____4437 =
                                  let uu____4438 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4438 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4437 in
                              [uu____4428] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4427
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4491 =
                              let uu____4492 =
                                let uu____4501 =
                                  let uu____4502 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4502 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4501 in
                              [uu____4492] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4491
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
          let uu____4576 =
            let uu____4577 = FStar_Syntax_Subst.compress dt1 in
            uu____4577.FStar_Syntax_Syntax.n in
          match uu____4576 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4581) ->
              let dbs1 =
                let uu____4611 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4611 in
              let dbs2 =
                let uu____4661 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4661 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4674 =
                           let uu____4675 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           [uu____4675] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____4674
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4706 =
                           let uu____4707 = FStar_Ident.string_of_lid ty_lid in
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             uu____4707 in
                         FStar_TypeChecker_Util.label uu____4706 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4713 =
                       let uu____4714 =
                         let uu____4723 =
                           let uu____4724 = FStar_Syntax_Subst.close [b] t in
                           FStar_Syntax_Util.abs
                             [((FStar_Pervasives_Native.fst b),
                                FStar_Pervasives_Native.None)] uu____4724
                             FStar_Pervasives_Native.None in
                         FStar_Syntax_Syntax.as_arg uu____4723 in
                       [uu____4714] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu____4713 FStar_Range.dummyRange) dbs3 cond
          | uu____4771 -> FStar_Syntax_Util.t_true
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
                  (lid, uu____4861, uu____4862, uu____4863, uu____4864,
                   uu____4865)
                  -> lid
              | uu____4874 -> failwith "Impossible!" in
            let uu____4875 = acc in
            match uu____4875 with
            | (uu____4912, en, uu____4914, uu____4915) ->
                let uu____4936 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____4936 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____4973 = acc in
                     (match uu____4973 with
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
                                     (uu____5047, uu____5048, uu____5049,
                                      t_lid, uu____5051, uu____5052)
                                     -> t_lid = lid
                                 | uu____5057 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5070 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5070)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5073 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5076 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5073, uu____5076)))
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
          let uu____5133 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5143, us, uu____5145, t, uu____5147, uu____5148) ->
                (us, t)
            | uu____5157 -> failwith "Impossible!" in
          match uu____5133 with
          | (us, t) ->
              let uu____5166 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____5166 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     let uu____5191 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu____5191 with
                     | (axioms, env2, guard, cond) ->
                         let phi =
                           let uu____5269 = FStar_Syntax_Util.arrow_formals t in
                           match uu____5269 with
                           | (uu____5276, t1) ->
                               let uu____5282 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu____5282
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu____5284 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                         (match uu____5284 with
                          | (phi1, uu____5292) ->
                              ((let uu____5294 =
                                  FStar_TypeChecker_Env.should_verify env2 in
                                if uu____5294
                                then
                                  let uu____5295 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5295
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l ->
                                       fun uu____5312 ->
                                         match uu____5312 with
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
                                                    = [];
                                                  FStar_Syntax_Syntax.sigopts
                                                    =
                                                    FStar_Pervasives_Native.None
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
                let uu____5380 =
                  let uu____5381 = FStar_Syntax_Subst.compress t in
                  uu____5381.FStar_Syntax_Syntax.n in
                match uu____5380 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5388) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5425 = is_mutual t' in
                    if uu____5425
                    then true
                    else
                      (let uu____5427 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5427)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5447) ->
                    is_mutual t'
                | uu____5452 -> false
              and exists_mutual uu___1_5453 =
                match uu___1_5453 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5472 =
                let uu____5473 = FStar_Syntax_Subst.compress dt1 in
                uu____5473.FStar_Syntax_Syntax.n in
              match uu____5472 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5479) ->
                  let dbs1 =
                    let uu____5509 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5509 in
                  let dbs2 =
                    let uu____5559 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5559 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5577 =
                               let uu____5578 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                               [uu____5578] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.t_haseq uu____5577
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5608 = is_mutual sort in
                             if uu____5608
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5618 =
                             let uu____5619 =
                               let uu____5628 =
                                 let uu____5629 =
                                   FStar_Syntax_Subst.close [b] t in
                                 FStar_Syntax_Util.abs
                                   [((FStar_Pervasives_Native.fst b),
                                      FStar_Pervasives_Native.None)]
                                   uu____5629 FStar_Pervasives_Native.None in
                               FStar_Syntax_Syntax.as_arg uu____5628 in
                             [uu____5619] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.tforall uu____5618
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5676 -> acc
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
              let uu____5725 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____5747, bs, t, uu____5750, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5762 -> failwith "Impossible!" in
              match uu____5725 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____5785 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____5785 t in
                  let uu____5794 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____5794 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____5804 =
                           let uu____5805 = FStar_Syntax_Subst.compress t2 in
                           uu____5805.FStar_Syntax_Syntax.n in
                         match uu____5804 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5809) ->
                             ibs
                         | uu____5830 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____5839 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____5840 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5839
                           uu____5840 in
                       let ind1 =
                         let uu____5844 =
                           FStar_List.map
                             (fun uu____5861 ->
                                match uu____5861 with
                                | (bv, aq) ->
                                    let uu____5880 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5880, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____5844
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____5884 =
                           FStar_List.map
                             (fun uu____5901 ->
                                match uu____5901 with
                                | (bv, aq) ->
                                    let uu____5920 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5920, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5884
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____5924 =
                           let uu____5925 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____5925] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____5924
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5961, uu____5962, uu____5963, t_lid,
                                   uu____5965, uu____5966)
                                  -> t_lid = lid
                              | uu____5971 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___914_5981 = fml in
                         let uu____5982 =
                           let uu____5983 =
                             let uu____5990 =
                               let uu____5991 =
                                 let uu____6012 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu____6017 =
                                   let uu____6030 =
                                     let uu____6041 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu____6041] in
                                   [uu____6030] in
                                 (uu____6012, uu____6017) in
                               FStar_Syntax_Syntax.Meta_pattern uu____5991 in
                             (fml, uu____5990) in
                           FStar_Syntax_Syntax.Tm_meta uu____5983 in
                         {
                           FStar_Syntax_Syntax.n = uu____5982;
                           FStar_Syntax_Syntax.pos =
                             (uu___914_5981.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___914_5981.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6110 =
                                  let uu____6111 =
                                    let uu____6120 =
                                      let uu____6121 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6121
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6120 in
                                  [uu____6111] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6110
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6174 =
                                  let uu____6175 =
                                    let uu____6184 =
                                      let uu____6185 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6185
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6184 in
                                  [uu____6175] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6174
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
                     (lid, uu____6276, uu____6277, uu____6278, uu____6279,
                      uu____6280)
                     -> lid
                 | uu____6289 -> failwith "Impossible!") tcs in
          let uu____6290 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6302, uu____6303, uu____6304, uu____6305) ->
                (lid, us)
            | uu____6314 -> failwith "Impossible!" in
          match uu____6290 with
          | (lid, us) ->
              let uu____6323 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6323 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6350 =
                       let uu____6351 =
                         let uu____6358 = get_haseq_axiom_lid lid in
                         (uu____6358, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6351 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6350;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = [];
                       FStar_Syntax_Syntax.sigopts =
                         FStar_Pervasives_Native.None
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
          let uu____6411 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6437 ->
                    match uu___2_6437 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6438;
                        FStar_Syntax_Syntax.sigrng = uu____6439;
                        FStar_Syntax_Syntax.sigquals = uu____6440;
                        FStar_Syntax_Syntax.sigmeta = uu____6441;
                        FStar_Syntax_Syntax.sigattrs = uu____6442;
                        FStar_Syntax_Syntax.sigopts = uu____6443;_} -> true
                    | uu____6466 -> false)) in
          match uu____6411 with
          | (tys, datas) ->
              ((let uu____6488 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6498 ->
                          match uu___3_6498 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6499;
                              FStar_Syntax_Syntax.sigrng = uu____6500;
                              FStar_Syntax_Syntax.sigquals = uu____6501;
                              FStar_Syntax_Syntax.sigmeta = uu____6502;
                              FStar_Syntax_Syntax.sigattrs = uu____6503;
                              FStar_Syntax_Syntax.sigopts = uu____6504;_} ->
                              false
                          | uu____6525 -> true)) in
                if uu____6488
                then
                  let uu____6526 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6526
                else ());
               (let univs =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6534 =
                       let uu____6535 = FStar_List.hd tys in
                       uu____6535.FStar_Syntax_Syntax.sigel in
                     match uu____6534 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6538, uvs, uu____6540, uu____6541,
                          uu____6542, uu____6543)
                         -> uvs
                     | uu____6552 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6556 =
                  FStar_List.fold_right
                    (fun tc ->
                       fun uu____6595 ->
                         match uu____6595 with
                         | (env1, all_tcs, g) ->
                             let uu____6635 = tc_tycon env1 tc in
                             (match uu____6635 with
                              | (env2, tc1, tc_u, guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____6662 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____6662
                                    then
                                      let uu____6663 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____6663
                                    else ());
                                   (let uu____6665 =
                                      let uu____6666 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6666 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____6665))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard) in
                match uu____6556 with
                | (env1, tcs, g) ->
                    let uu____6712 =
                      FStar_List.fold_right
                        (fun se ->
                           fun uu____6734 ->
                             match uu____6734 with
                             | (datas1, g1) ->
                                 let uu____6753 =
                                   let uu____6758 = tc_data env1 tcs in
                                   uu____6758 se in
                                 (match uu____6753 with
                                  | (data, g') ->
                                      let uu____6775 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____6775))) datas
                        ([], g) in
                    (match uu____6712 with
                     | (datas1, g1) ->
                         let uu____6796 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             let uu___1025_6813 = g1 in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1025_6813.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (uu___1025_6813.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1025_6813.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1025_6813.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu____6823 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu____6823
                            then
                              let uu____6824 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____6824
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____6836 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs in
                              (uu____6836, datas1)) in
                         (match uu____6796 with
                          | (tcs1, datas2) ->
                              let sig_bndle =
                                let uu____6868 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____6869 =
                                  FStar_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____6868;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____6869;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                } in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l, univs1, binders, typ,
                                            uu____6895, uu____6896)
                                           ->
                                           let fail expected inferred =
                                             let uu____6916 =
                                               let uu____6921 =
                                                 let uu____6922 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu____6923 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____6922 uu____6923 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____6921) in
                                             FStar_Errors.raise_error
                                               uu____6916
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu____6924 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____6924 with
                                            | FStar_Pervasives_Native.None ->
                                                ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ, uu____6940) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____6971 ->
                                                        let uu____6972 =
                                                          let uu____6973 =
                                                            let uu____6988 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                typ in
                                                            (binders,
                                                              uu____6988) in
                                                          FStar_Syntax_Syntax.Tm_arrow
                                                            uu____6973 in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____6972
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs1, body) in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ))
                                                then
                                                  let uu____7009 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____7009 with
                                                   | (uu____7014, inferred)
                                                       ->
                                                       let uu____7016 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ in
                                                       (match uu____7016 with
                                                        | (uu____7021,
                                                           expected) ->
                                                            let uu____7023 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected in
                                                            if uu____7023
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ
                                                                inferred_typ))
                                                else
                                                  fail expected_typ
                                                    inferred_typ)
                                       | uu____7026 -> ()));
                               (sig_bndle, tcs1, datas2))))))
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"]
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.fv_qual ->
        Prims.bool ->
          FStar_TypeChecker_Env.env ->
            FStar_Ident.lident ->
              FStar_Ident.lident ->
                FStar_Syntax_Syntax.univ_names ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.binders ->
                        Prims.bool -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun attrs ->
      fun fvq ->
        fun refine_domain ->
          fun env ->
            fun tc ->
              fun lid ->
                fun uvs ->
                  fun inductive_tps ->
                    fun indices ->
                      fun fields ->
                        fun erasable ->
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
                              let uu____7130 =
                                let uu____7131 =
                                  let uu____7138 =
                                    let uu____7141 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7141 in
                                  (uu____7138, inst_univs) in
                                FStar_Syntax_Syntax.Tm_uinst uu____7131 in
                              FStar_Syntax_Syntax.mk uu____7130 p in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7175 ->
                                      match uu____7175 with
                                      | (x, imp) ->
                                          let uu____7194 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____7194, imp))) in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args p in
                          let unrefined_arg_binder =
                            let uu____7198 = projectee arg_typ in
                            FStar_Syntax_Syntax.mk_binder uu____7198 in
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
                                   let uu____7219 =
                                     FStar_Ident.set_lid_range disc_name p in
                                   FStar_Syntax_Syntax.fvar uu____7219
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None in
                                 let uu____7220 =
                                   let uu____7223 =
                                     let uu____7226 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs in
                                     let uu____7227 =
                                       let uu____7228 =
                                         let uu____7237 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7237 in
                                       [uu____7228] in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7226
                                       uu____7227 p in
                                   FStar_Syntax_Util.b2t uu____7223 in
                                 FStar_Syntax_Util.refine x uu____7220 in
                               let uu____7262 =
                                 let uu___1100_7263 = projectee arg_typ in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1100_7263.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1100_7263.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 } in
                               FStar_Syntax_Syntax.mk_binder uu____7262) in
                          let ntps = FStar_List.length tps in
                          let all_params =
                            let uu____7280 =
                              FStar_List.map
                                (fun uu____7304 ->
                                   match uu____7304 with
                                   | (x, uu____7318) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps in
                            FStar_List.append uu____7280 fields in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7377 ->
                                    match uu____7377 with
                                    | (x, uu____7391) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)))) in
                          let early_prims_inductive =
                            (let uu____7401 =
                               FStar_TypeChecker_Env.current_module env in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7401)
                              &&
                              (FStar_List.existsb
                                 (fun s ->
                                    let uu____7405 =
                                      let uu____7406 =
                                        FStar_Ident.ident_of_lid tc in
                                      FStar_Ident.string_of_id uu____7406 in
                                    s = uu____7405) early_prims_inductives) in
                          let discriminator_ses =
                            if fvq <> FStar_Syntax_Syntax.Data_ctor
                            then []
                            else
                              (let discriminator_name =
                                 FStar_Syntax_Util.mk_discriminator lid in
                               let no_decl = false in
                               let only_decl =
                                 early_prims_inductive ||
                                   (let uu____7417 =
                                      let uu____7418 =
                                        FStar_TypeChecker_Env.current_module
                                          env in
                                      FStar_Ident.string_of_lid uu____7418 in
                                    FStar_Options.dont_gen_projectors
                                      uu____7417) in
                               let quals =
                                 let uu____7422 =
                                   FStar_List.filter
                                     (fun uu___4_7426 ->
                                        match uu___4_7426 with
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                            -> true
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu____7427 -> false) iquals in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____7422 in
                               let binders =
                                 FStar_List.append imp_binders
                                   [unrefined_arg_binder] in
                               let t =
                                 let bool_typ =
                                   if erasable
                                   then
                                     FStar_Syntax_Syntax.mk_GTotal
                                       FStar_Syntax_Util.t_bool
                                   else
                                     FStar_Syntax_Syntax.mk_Total
                                       FStar_Syntax_Util.t_bool in
                                 let uu____7467 =
                                   FStar_Syntax_Util.arrow binders bool_typ in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____7467 in
                               let decl =
                                 let uu____7471 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____7471;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               (let uu____7473 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes") in
                                if uu____7473
                                then
                                  let uu____7474 =
                                    FStar_Syntax_Print.sigelt_to_string decl in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____7474
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
                                                 fun uu____7525 ->
                                                   match uu____7525 with
                                                   | (x, imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____7545 =
                                                           let uu____7548 =
                                                             let uu____7549 =
                                                               let uu____7556
                                                                 =
                                                                 let uu____7557
                                                                   =
                                                                   FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   uu____7557
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun in
                                                               (uu____7556,
                                                                 FStar_Syntax_Syntax.tun) in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____7549 in
                                                           pos uu____7548 in
                                                         (uu____7545, b)
                                                       else
                                                         (let uu____7563 =
                                                            let uu____7566 =
                                                              let uu____7567
                                                                =
                                                                let uu____7568
                                                                  =
                                                                  FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  uu____7568
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____7567 in
                                                            pos uu____7566 in
                                                          (uu____7563, b)))) in
                                       let pat_true =
                                         let uu____7586 =
                                           let uu____7589 =
                                             let uu____7590 =
                                               let uu____7603 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq) in
                                               (uu____7603, arg_pats) in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____7590 in
                                           pos uu____7589 in
                                         (uu____7586,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool) in
                                       let pat_false =
                                         let uu____7637 =
                                           let uu____7640 =
                                             let uu____7641 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____7641 in
                                           pos uu____7640 in
                                         (uu____7637,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool) in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder) in
                                       let uu____7655 =
                                         let uu____7656 =
                                           let uu____7679 =
                                             let uu____7696 =
                                               FStar_Syntax_Util.branch
                                                 pat_true in
                                             let uu____7711 =
                                               let uu____7728 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false in
                                               [uu____7728] in
                                             uu____7696 :: uu____7711 in
                                           (arg_exp, uu____7679) in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____7656 in
                                       FStar_Syntax_Syntax.mk uu____7655 p) in
                                  let dd =
                                    FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one in
                                  let imp =
                                    FStar_Syntax_Util.abs binders body
                                      FStar_Pervasives_Native.None in
                                  let lbtyp =
                                    if no_decl
                                    then t
                                    else FStar_Syntax_Syntax.tun in
                                  let lb =
                                    let uu____7814 =
                                      let uu____7819 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None in
                                      FStar_Util.Inr uu____7819 in
                                    let uu____7820 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____7814 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____7820 [] FStar_Range.dummyRange in
                                  let impl =
                                    let uu____7826 =
                                      let uu____7827 =
                                        let uu____7834 =
                                          let uu____7837 =
                                            let uu____7838 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right in
                                            FStar_All.pipe_right uu____7838
                                              (fun fv ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                          [uu____7837] in
                                        ((false, [lb]), uu____7834) in
                                      FStar_Syntax_Syntax.Sig_let uu____7827 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____7826;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    } in
                                  (let uu____7850 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes") in
                                   if uu____7850
                                   then
                                     let uu____7851 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____7851
                                   else ());
                                  [decl; impl])) in
                          let arg_exp =
                            FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst arg_binder) in
                          let binders =
                            FStar_List.append imp_binders [arg_binder] in
                          let arg =
                            FStar_Syntax_Util.arg_of_non_null_binder
                              arg_binder in
                          let subst =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i ->
                                    fun uu____7919 ->
                                      match uu____7919 with
                                      | (a, uu____7927) ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i in
                                          let field_proj_tm =
                                            let uu____7934 =
                                              let uu____7935 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____7935 in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu____7934 inst_univs in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p in
                                          FStar_Syntax_Syntax.NT (a, proj))) in
                          let projectors_ses =
                            let uu____7958 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu____7998 ->
                                        match uu____7998 with
                                        | (x, uu____8008) ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x in
                                            let field_name =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i in
                                            let t =
                                              let result_comp =
                                                let t =
                                                  FStar_Syntax_Subst.subst
                                                    subst
                                                    x.FStar_Syntax_Syntax.sort in
                                                if erasable
                                                then
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                else
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t in
                                              let uu____8025 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu____8025 in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu____8030 =
                                                   let uu____8031 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env in
                                                   FStar_Ident.string_of_lid
                                                     uu____8031 in
                                                 FStar_Options.dont_gen_projectors
                                                   uu____8030) in
                                            let no_decl = false in
                                            let quals q =
                                              if only_decl
                                              then
                                                FStar_Syntax_Syntax.Assumption
                                                :: q
                                              else q in
                                            let quals1 =
                                              let iquals1 =
                                                FStar_All.pipe_right iquals
                                                  (FStar_List.filter
                                                     (fun uu___5_8059 ->
                                                        match uu___5_8059
                                                        with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                            -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                            -> true
                                                        | FStar_Syntax_Syntax.Private
                                                            -> true
                                                        | uu____8060 -> false)) in
                                              quals
                                                ((FStar_Syntax_Syntax.Projector
                                                    (lid,
                                                      (x.FStar_Syntax_Syntax.ppname)))
                                                :: iquals1) in
                                            let attrs1 =
                                              FStar_List.append
                                                (if only_decl
                                                 then []
                                                 else
                                                   [FStar_Syntax_Util.attr_substitute])
                                                attrs in
                                            let decl =
                                              let uu____8068 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu____8068;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu____8070 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes") in
                                              if uu____8070
                                              then
                                                let uu____8071 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu____8071
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu____8077 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu____8077
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_All.pipe_right
                                                    all_params
                                                    (FStar_List.mapi
                                                       (fun j ->
                                                          fun uu____8118 ->
                                                            match uu____8118
                                                            with
                                                            | (x1, imp) ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu____8138
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                  (uu____8138,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____8150
                                                                    =
                                                                    let uu____8153
                                                                    =
                                                                    let uu____8154
                                                                    =
                                                                    let uu____8161
                                                                    =
                                                                    let uu____8162
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8162
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8161,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8154 in
                                                                    pos
                                                                    uu____8153 in
                                                                    (uu____8150,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____8168
                                                                    =
                                                                    let uu____8171
                                                                    =
                                                                    let uu____8172
                                                                    =
                                                                    let uu____8173
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8173
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8172 in
                                                                    pos
                                                                    uu____8171 in
                                                                    (uu____8168,
                                                                    b)))) in
                                                let pat =
                                                  let uu____8191 =
                                                    let uu____8194 =
                                                      let uu____8195 =
                                                        let uu____8208 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu____8208,
                                                          arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____8195 in
                                                    pos uu____8194 in
                                                  let uu____8217 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu____8191,
                                                    FStar_Pervasives_Native.None,
                                                    uu____8217) in
                                                let body =
                                                  let uu____8233 =
                                                    let uu____8234 =
                                                      let uu____8257 =
                                                        let uu____8274 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu____8274] in
                                                      (arg_exp, uu____8257) in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu____8234 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____8233 p1 in
                                                let imp =
                                                  FStar_Syntax_Util.abs
                                                    binders body
                                                    FStar_Pervasives_Native.None in
                                                let dd =
                                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                                    Prims.int_one in
                                                let lbtyp =
                                                  if no_decl
                                                  then t
                                                  else
                                                    FStar_Syntax_Syntax.tun in
                                                let lb =
                                                  let uu____8346 =
                                                    let uu____8351 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Util.Inr uu____8351 in
                                                  let uu____8352 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____8346;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____8352;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  } in
                                                let impl =
                                                  let uu____8358 =
                                                    let uu____8359 =
                                                      let uu____8366 =
                                                        let uu____8369 =
                                                          let uu____8370 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right in
                                                          FStar_All.pipe_right
                                                            uu____8370
                                                            (fun fv ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [uu____8369] in
                                                      ((false, [lb]),
                                                        uu____8366) in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____8359 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____8358;
                                                    FStar_Syntax_Syntax.sigrng
                                                      = p1;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = quals1;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      =
                                                      FStar_Syntax_Syntax.default_sigmeta;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = attrs1;
                                                    FStar_Syntax_Syntax.sigopts
                                                      =
                                                      FStar_Pervasives_Native.None
                                                  } in
                                                (let uu____8382 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes") in
                                                 if uu____8382
                                                 then
                                                   let uu____8383 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu____8383
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl])))) in
                            FStar_All.pipe_right uu____7958
                              FStar_List.flatten in
                          FStar_List.append discriminator_ses projectors_ses
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun attrs ->
      fun env ->
        fun tcs ->
          fun se ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_datacon
                (constr_lid, uvs, t, typ_lid, n_typars, uu____8440) when
                let uu____8445 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid in
                Prims.op_Negation uu____8445 ->
                let uu____8446 = FStar_Syntax_Subst.univ_var_opening uvs in
                (match uu____8446 with
                 | (univ_opening, uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t in
                     let uu____8468 = FStar_Syntax_Util.arrow_formals t1 in
                     (match uu____8468 with
                      | (formals, uu____8478) ->
                          let uu____8483 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1 ->
                                   let uu____8515 =
                                     let uu____8516 =
                                       let uu____8517 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____8517 in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____8516 in
                                   if uu____8515
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____8536, uvs', tps, typ0,
                                          uu____8540, constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____8557 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None) in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                let uu____8598 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid in
                                if uu____8598
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng in
                          (match uu____8483 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0 in
                               let uu____8625 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu____8625 with
                                | (indices, uu____8635) ->
                                    let refine_domain =
                                      let uu____8641 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___6_8646 ->
                                                match uu___6_8646 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____8647 -> true
                                                | uu____8656 -> false)) in
                                      if uu____8641
                                      then false
                                      else should_refine in
                                    let fv_qual =
                                      let filter_records uu___7_8666 =
                                        match uu___7_8666 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____8669, fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu____8681 ->
                                            FStar_Pervasives_Native.None in
                                      let uu____8682 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu____8682 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu____8687 =
                                        FStar_Util.first_N n_typars formals in
                                      match uu____8687 with
                                      | (imp_tps, fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____8770 ->
                                                 fun uu____8771 ->
                                                   match (uu____8770,
                                                           uu____8771)
                                                   with
                                                   | ((x, uu____8797),
                                                      (x', uu____8799)) ->
                                                       let uu____8820 =
                                                         let uu____8827 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu____8827) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____8820) imp_tps
                                              inductive_tps1 in
                                          FStar_Syntax_Subst.subst_binders
                                            rename fields in
                                    let erasable =
                                      FStar_Syntax_Util.has_attribute
                                        se.FStar_Syntax_Syntax.sigattrs
                                        FStar_Parser_Const.erasable_attr in
                                    mk_discriminator_and_indexed_projectors
                                      iquals attrs fv_qual refine_domain env
                                      typ_lid constr_lid uvs1 inductive_tps1
                                      indices fields erasable))))
            | uu____8833 -> []