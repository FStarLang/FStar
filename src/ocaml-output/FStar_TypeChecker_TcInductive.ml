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
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc) in
                                              (uu____433,
                                                (let uu___60_439 = s in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___60_439.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___60_439.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___60_439.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___60_439.FStar_Syntax_Syntax.sigattrs);
                                                   FStar_Syntax_Syntax.sigopts
                                                     =
                                                     (uu___60_439.FStar_Syntax_Syntax.sigopts)
                                                 }), u, guard1)))))))))
      | uu____444 -> failwith "impossible"
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
            let uu____504 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu____504 with
             | (usubst, _uvs1) ->
                 let uu____527 =
                   let uu____532 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu____533 = FStar_Syntax_Subst.subst usubst t in
                   (uu____532, uu____533) in
                 (match uu____527 with
                  | (env1, t1) ->
                      let uu____540 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____579 ->
                               match uu____579 with
                               | (se1, u_tc) ->
                                   let uu____594 =
                                     let uu____595 =
                                       let uu____596 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____596 in
                                     FStar_Ident.lid_equals tc_lid uu____595 in
                                   if uu____594
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____615, uu____616, tps,
                                           uu____618, uu____619, uu____620)
                                          ->
                                          let tps1 =
                                            let uu____630 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu____630
                                              (FStar_List.map
                                                 (fun uu____670 ->
                                                    match uu____670 with
                                                    | (x, uu____684) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag)))) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu____692 =
                                            let uu____699 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu____699, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu____692
                                      | uu____706 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu____747 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu____747
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu____540 with
                       | (env2, tps, u_tc) ->
                           let uu____774 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu____782 =
                               let uu____783 = FStar_Syntax_Subst.compress t2 in
                               uu____783.FStar_Syntax_Syntax.n in
                             match uu____782 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu____814 = FStar_Util.first_N ntps bs in
                                 (match uu____814 with
                                  | (uu____847, bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          t2.FStar_Syntax_Syntax.pos in
                                      let subst =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i ->
                                                fun uu____918 ->
                                                  match uu____918 with
                                                  | (x, uu____926) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            (Prims.int_one +
                                                               i)), x))) in
                                      let uu____931 =
                                        let uu____936 =
                                          FStar_Syntax_Subst.subst subst t3 in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu____936 in
                                      (match uu____931 with
                                       | (bs1, c1) ->
                                           let uu____945 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1) in
                                           if uu____945
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu____955 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1) in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu____955)))
                             | uu____962 -> ([], t2) in
                           (match uu____774 with
                            | (arguments, result) ->
                                ((let uu____982 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu____982
                                  then
                                    let uu____983 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu____984 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu____985 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____983 uu____984 uu____985
                                  else ());
                                 (let uu____987 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu____987 with
                                  | (arguments1, env', us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          result.FStar_Syntax_Syntax.pos in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc in
                                      let uu____1005 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result in
                                      (match uu____1005 with
                                       | (result1, res_lcomp) ->
                                           let uu____1016 =
                                             FStar_Syntax_Util.head_and_args
                                               result1 in
                                           (match uu____1016 with
                                            | (head, args) ->
                                                let p_args =
                                                  let uu____1074 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1074 in
                                                (FStar_List.iter2
                                                   (fun uu____1156 ->
                                                      fun uu____1157 ->
                                                        match (uu____1156,
                                                                uu____1157)
                                                        with
                                                        | ((bv, uu____1187),
                                                           (t2, uu____1189))
                                                            ->
                                                            let uu____1216 =
                                                              let uu____1217
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2 in
                                                              uu____1217.FStar_Syntax_Syntax.n in
                                                            (match uu____1216
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1221 ->
                                                                 let uu____1222
                                                                   =
                                                                   let uu____1227
                                                                    =
                                                                    let uu____1228
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu____1229
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1228
                                                                    uu____1229 in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1227) in
                                                                 FStar_Errors.raise_error
                                                                   uu____1222
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1231 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                    FStar_All.pipe_right
                                                      uu____1231
                                                      FStar_Syntax_Util.unrefine in
                                                  (let uu____1233 =
                                                     let uu____1234 =
                                                       FStar_Syntax_Subst.compress
                                                         ty in
                                                     uu____1234.FStar_Syntax_Syntax.n in
                                                   match uu____1233 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1237 -> ()
                                                   | uu____1238 ->
                                                       let uu____1239 =
                                                         let uu____1244 =
                                                           let uu____1245 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1 in
                                                           let uu____1246 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1245
                                                             uu____1246 in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1244) in
                                                       FStar_Errors.raise_error
                                                         uu____1239
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1248 =
                                                       let uu____1249 =
                                                         FStar_Syntax_Subst.compress
                                                           head in
                                                       uu____1249.FStar_Syntax_Syntax.n in
                                                     match uu____1248 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1253;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1254;_},
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
                                                                    let uu____1267
                                                                    =
                                                                    let uu____1268
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Range.dummyRange in
                                                                    let uu____1269
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____1268
                                                                    uu____1269 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1267)
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
                                                     | uu____1272 ->
                                                         let uu____1273 =
                                                           let uu____1278 =
                                                             let uu____1279 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid in
                                                             let uu____1280 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1279
                                                               uu____1280 in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1278) in
                                                         FStar_Errors.raise_error
                                                           uu____1273
                                                           se.FStar_Syntax_Syntax.sigrng in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g ->
                                                          fun uu____1295 ->
                                                            fun u_x ->
                                                              match uu____1295
                                                              with
                                                              | (x,
                                                                 uu____1304)
                                                                  ->
                                                                  let uu____1309
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1309)
                                                       g_uvs arguments1 us in
                                                   let t2 =
                                                     let uu____1313 =
                                                       let uu____1322 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1362
                                                                 ->
                                                                 match uu____1362
                                                                 with
                                                                 | (x,
                                                                    uu____1376)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                       FStar_List.append
                                                         uu____1322
                                                         arguments1 in
                                                     let uu____1389 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1 in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1313 uu____1389 in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2 in
                                                   ((let uu___186_1394 = se in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___186_1394.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___186_1394.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___186_1394.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___186_1394.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___186_1394.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1397 -> failwith "impossible"
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
               (fun uu____1486 ->
                  match uu____1486 with
                  | (se, uu____1492) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1493, uu____1494, tps, k, uu____1497,
                            uu____1498)
                           ->
                           let uu____1507 =
                             let uu____1508 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1508 in
                           FStar_Syntax_Syntax.null_binder uu____1507
                       | uu____1513 -> failwith "Impossible"))) in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1541, uu____1542, t, uu____1544, uu____1545,
                       uu____1546)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1551 -> failwith "Impossible")) in
        let t =
          let uu____1555 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1555 in
        (let uu____1565 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu____1565
         then
           let uu____1566 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1566
         else ());
        (let uu____1568 = FStar_TypeChecker_Util.generalize_universes env t in
         match uu____1568 with
         | (uvs, t1) ->
             ((let uu____1588 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu____1588
               then
                 let uu____1589 =
                   let uu____1590 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u -> FStar_Ident.string_of_id u)) in
                   FStar_All.pipe_right uu____1590 (FStar_String.concat ", ") in
                 let uu____1601 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1589 uu____1601
               else ());
              (let uu____1603 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu____1603 with
               | (uvs1, t2) ->
                   let uu____1618 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu____1618 with
                    | (args, uu____1634) ->
                        let uu____1639 =
                          FStar_Util.first_N (FStar_List.length binders) args in
                        (match uu____1639 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1744 ->
                                    fun uu____1745 ->
                                      match (uu____1744, uu____1745) with
                                      | ((x, uu____1767), (se, uu____1769))
                                          ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu____1785, tps,
                                                uu____1787, mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu____1799 =
                                                 let uu____1804 =
                                                   let uu____1805 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu____1805.FStar_Syntax_Syntax.n in
                                                 match uu____1804 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu____1834 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1 in
                                                     (match uu____1834 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____1912 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu____1931 -> ([], ty) in
                                               (match uu____1799 with
                                                | (tps1, t3) ->
                                                    let uu___263_1940 = se in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___263_1940.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___263_1940.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___263_1940.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___263_1940.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___263_1940.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____1945 ->
                                               failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____1951 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun uu____1955 ->
                                             FStar_Syntax_Syntax.U_name
                                               uu____1955)) in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_1975 ->
                                             match uu___0_1975 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu____1981,
                                                    uu____1982, uu____1983,
                                                    uu____1984, uu____1985);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____1986;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____1987;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____1988;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____1989;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____1990;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2005 ->
                                                 failwith "Impossible")) in
                                   FStar_List.map2
                                     (fun uu____2028 ->
                                        fun d ->
                                          match uu____2028 with
                                          | (t3, uu____2037) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu____2043,
                                                    uu____2044, tc, ntps,
                                                    mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2053 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_All.pipe_right
                                                       uu____2053
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   let uu___300_2054 = d in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___300_2054.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___300_2054.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___300_2054.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___300_2054.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___300_2054.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2057 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env ->
    fun msg ->
      let uu____2077 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____2077
      then
        let uu____2078 =
          let uu____2079 =
            let uu____2080 = msg () in Prims.op_Hat uu____2080 "\n" in
          Prims.op_Hat "Positivity::" uu____2079 in
        FStar_Util.print_string uu____2078
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____2092 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____2092
let rec (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____2112 =
      let uu____2113 = FStar_Syntax_Subst.compress t in
      uu____2113.FStar_Syntax_Syntax.n in
    match uu____2112 with
    | FStar_Syntax_Syntax.Tm_name uu____2122 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives_Native.Some (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu____2138 =
          let uu____2139 = FStar_Syntax_Subst.compress t1 in
          uu____2139.FStar_Syntax_Syntax.n in
        (match uu____2138 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, us)
         | uu____2153 ->
             failwith
               "try_get_fv: Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2161, uu____2162) ->
        try_get_fv t1
    | uu____2203 ->
        let uu____2204 =
          let uu____2205 = FStar_Syntax_Print.tag_of_term t in
          Prims.op_Hat "try_get_fv: did not expect t to be a : " uu____2205 in
        failwith uu____2204
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
          let uu____2240 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2276 ->
               match uu____2276 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2319 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2319 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2240
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
            (fun uu____2515 ->
               let uu____2516 = FStar_Syntax_Print.term_to_string btype in
               Prims.op_Hat "Checking strict positivity in type: " uu____2516);
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
             (fun uu____2521 ->
                let uu____2522 = FStar_Syntax_Print.term_to_string btype1 in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2522);
           (let uu____2525 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2525) ||
             ((debug_log env
                 (fun uu____2534 ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2535 =
                  let uu____2536 = FStar_Syntax_Subst.compress btype1 in
                  uu____2536.FStar_Syntax_Syntax.n in
                match uu____2535 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let fv_us_opt = try_get_fv t in
                    let uu____2572 =
                      FStar_All.pipe_right fv_us_opt FStar_Util.is_none in
                    if uu____2572
                    then true
                    else
                      (let uu____2584 =
                         FStar_All.pipe_right fv_us_opt FStar_Util.must in
                       match uu____2584 with
                       | (fv, us) ->
                           let uu____2605 =
                             FStar_Ident.lid_equals
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               ty_lid in
                           if uu____2605
                           then
                             (debug_log env
                                (fun uu____2608 ->
                                   "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                              FStar_List.for_all
                                (fun uu____2619 ->
                                   match uu____2619 with
                                   | (t1, uu____2627) ->
                                       let uu____2632 =
                                         ty_occurs_in ty_lid t1 in
                                       Prims.op_Negation uu____2632) args)
                           else
                             (debug_log env
                                (fun uu____2636 ->
                                   "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                              ty_nested_positive_in_inductive ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env
                       (fun uu____2661 ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp =
                        let c1 =
                          let uu____2666 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu____2666
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2670 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu____2670
                             (FStar_List.existsb
                                (fun q -> q = FStar_Syntax_Syntax.TotalEffect))) in
                      if Prims.op_Negation check_comp
                      then
                        (debug_log env
                           (fun uu____2679 ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2683 ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2694 ->
                               match uu____2694 with
                               | (b, uu____2702) ->
                                   let uu____2707 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2707) sbs)
                           &&
                           ((let uu____2712 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2712 with
                             | (uu____2717, return_type) ->
                                 let uu____2719 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2719)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2720 ->
                    (debug_log env
                       (fun uu____2723 ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2724 ->
                    (debug_log env
                       (fun uu____2727 ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2729) ->
                    (debug_log env
                       (fun uu____2736 ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2738) ->
                    (debug_log env
                       (fun uu____2745 ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2746, branches) ->
                    (debug_log env
                       (fun uu____2786 ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2806 ->
                          match uu____2806 with
                          | (p, uu____2818, t) ->
                              let bs =
                                let uu____2837 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2837 in
                              let uu____2846 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2846 with
                               | (bs1, t1) ->
                                   let uu____2853 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2853)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2855, uu____2856)
                    ->
                    (debug_log env
                       (fun uu____2899 ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2900 ->
                    (debug_log env
                       (fun uu____2904 ->
                          let uu____2905 =
                            let uu____2906 =
                              FStar_Syntax_Print.tag_of_term btype1 in
                            let uu____2907 =
                              let uu____2908 =
                                FStar_Syntax_Print.term_to_string btype1 in
                              Prims.op_Hat " and term: " uu____2908 in
                            Prims.op_Hat uu____2906 uu____2907 in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____2905);
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
                (fun uu____2918 ->
                   let uu____2919 =
                     let uu____2920 = FStar_Ident.string_of_lid ilid in
                     let uu____2921 =
                       let uu____2922 =
                         FStar_Syntax_Print.args_to_string args in
                       Prims.op_Hat " applied to arguments: " uu____2922 in
                     Prims.op_Hat uu____2920 uu____2921 in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____2919);
              (let uu____2923 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2923 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2936 =
                       let uu____2937 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       FStar_TypeChecker_Env.fv_has_attr env uu____2937
                         FStar_Parser_Const.assume_strictly_positive_attr_lid in
                     (if uu____2936
                      then
                        (debug_log env
                           (fun uu____2941 ->
                              let uu____2942 = FStar_Ident.string_of_lid ilid in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____2942);
                         true)
                      else
                        (debug_log env
                           (fun uu____2946 ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____2948 =
                        already_unfolded ilid args unfolded env in
                      if uu____2948
                      then
                        (debug_log env
                           (fun uu____2951 ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____2954 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu____2954 in
                         debug_log env
                           (fun uu____2960 ->
                              let uu____2961 =
                                let uu____2962 =
                                  FStar_Util.string_of_int num_ibs in
                                Prims.op_Hat uu____2962
                                  ", also adding to the memo table" in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____2961);
                         (let uu____2964 =
                            let uu____2965 = FStar_ST.op_Bang unfolded in
                            let uu____2978 =
                              let uu____2985 =
                                let uu____2990 =
                                  let uu____2991 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2991 in
                                (ilid, uu____2990) in
                              [uu____2985] in
                            FStar_List.append uu____2965 uu____2978 in
                          FStar_ST.op_Colon_Equals unfolded uu____2964);
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
                    (fun uu____3075 ->
                       let uu____3076 =
                         let uu____3077 = FStar_Ident.string_of_lid dlid in
                         let uu____3078 =
                           let uu____3079 = FStar_Ident.string_of_lid ilid in
                           Prims.op_Hat " of the inductive " uu____3079 in
                         Prims.op_Hat uu____3077 uu____3078 in
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         uu____3076);
                  (let uu____3080 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3080 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3104 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        debug_log env
                          (fun uu____3108 ->
                             let uu____3109 =
                               FStar_Syntax_Print.term_to_string dt in
                             Prims.op_Hat
                               "Checking nested positivity in the data constructor type: "
                               uu____3109);
                        (let uu____3110 =
                           let uu____3111 = FStar_Syntax_Subst.compress dt in
                           uu____3111.FStar_Syntax_Syntax.n in
                         match uu____3110 with
                         | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                             (debug_log env
                                (fun uu____3138 ->
                                   "Checked nested positivity in Tm_arrow data constructor type");
                              (let uu____3139 =
                                 FStar_List.splitAt num_ibs dbs in
                               match uu____3139 with
                               | (ibs, dbs1) ->
                                   let ibs1 =
                                     FStar_Syntax_Subst.open_binders ibs in
                                   let dbs2 =
                                     let uu____3202 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_binders
                                       uu____3202 dbs1 in
                                   let c1 =
                                     let uu____3206 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_comp uu____3206
                                       c in
                                   let uu____3209 =
                                     FStar_List.splitAt num_ibs args in
                                   (match uu____3209 with
                                    | (args1, uu____3243) ->
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
                                          let uu____3335 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length dbs3) subst in
                                          FStar_Syntax_Subst.subst_comp
                                            uu____3335 c1 in
                                        (debug_log env
                                           (fun uu____3347 ->
                                              let uu____3348 =
                                                let uu____3349 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    "; " dbs3 in
                                                let uu____3350 =
                                                  let uu____3351 =
                                                    FStar_Syntax_Print.comp_to_string
                                                      c2 in
                                                  Prims.op_Hat ", and c: "
                                                    uu____3351 in
                                                Prims.op_Hat uu____3349
                                                  uu____3350 in
                                              Prims.op_Hat
                                                "Checking nested positivity in the unfolded data constructor binders as: "
                                                uu____3348);
                                         ty_nested_positive_in_type ty_lid
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (dbs3, c2)) ilid num_ibs
                                           unfolded env))))
                         | uu____3362 ->
                             (debug_log env
                                (fun uu____3365 ->
                                   "Checking nested positivity in the data constructor type that is not an arrow");
                              (let uu____3366 =
                                 let uu____3367 =
                                   FStar_Syntax_Subst.compress dt in
                                 uu____3367.FStar_Syntax_Syntax.n in
                               ty_nested_positive_in_type ty_lid uu____3366
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
                     (fun uu____3404 ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3405 =
                      let uu____3410 = try_get_fv t1 in
                      FStar_All.pipe_right uu____3410 FStar_Util.must in
                    match uu____3405 with
                    | (fv, uu____3432) ->
                        let uu____3433 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____3433
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  (debug_log env
                     (fun uu____3460 ->
                        let uu____3461 =
                          FStar_Syntax_Print.binders_to_string "; " sbs in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3461);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3463 =
                      FStar_List.fold_left
                        (fun uu____3482 ->
                           fun b ->
                             match uu____3482 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3505 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3508 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3505, uu____3508))) (true, env)
                        sbs1 in
                    match uu____3463 with | (b, uu____3522) -> b))
              | uu____3523 ->
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
              let uu____3554 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3554 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3578 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3582 ->
                        let uu____3583 = FStar_Syntax_Print.term_to_string dt in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3583);
                   (let uu____3584 =
                      let uu____3585 = FStar_Syntax_Subst.compress dt in
                      uu____3585.FStar_Syntax_Syntax.n in
                    match uu____3584 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3588 ->
                        (debug_log env
                           (fun uu____3591 ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3593) ->
                        let dbs1 =
                          let uu____3623 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3623 in
                        let dbs2 =
                          let uu____3673 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3673 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        (debug_log env
                           (fun uu____3680 ->
                              let uu____3681 =
                                let uu____3682 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3) in
                                Prims.op_Hat uu____3682 " binders" in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3681);
                         (let uu____3689 =
                            FStar_List.fold_left
                              (fun uu____3708 ->
                                 fun b ->
                                   match uu____3708 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3731 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3734 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3731, uu____3734)))
                              (true, env) dbs3 in
                          match uu____3689 with | (b, uu____3748) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3749, uu____3750) ->
                        (debug_log env
                           (fun uu____3777 ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs) ->
                        (debug_log env
                           (fun uu____3786 ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3787 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3805 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____3821, uu____3822, uu____3823) ->
            (lid, us, bs)
        | uu____3832 -> failwith "Impossible!" in
      match uu____3805 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____3842 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3842 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3865 =
                 let uu____3868 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3868 in
               FStar_List.for_all
                 (fun d ->
                    let uu____3880 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3880
                      unfolded_inductives env2) uu____3865)
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
        (uu____3911, uu____3912, t, uu____3914, uu____3915, uu____3916) -> t
    | uu____3921 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = FStar_Ident.string_of_lid lid in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____3931 =
         let uu____3932 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____3932 haseq_suffix in
       uu____3931 = Prims.int_zero)
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____3938 =
      let uu____3939 = FStar_Ident.ns_of_lid lid in
      let uu____3942 =
        let uu____3945 =
          let uu____3946 =
            let uu____3947 =
              let uu____3948 = FStar_Ident.ident_of_lid lid in
              FStar_Ident.string_of_id uu____3948 in
            Prims.op_Hat uu____3947 haseq_suffix in
          FStar_Ident.id_of_text uu____3946 in
        [uu____3945] in
      FStar_List.append uu____3939 uu____3942 in
    FStar_Ident.lid_of_ids uu____3938
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
          let uu____3993 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4007, bs, t, uu____4010, uu____4011) ->
                (lid, bs, t)
            | uu____4020 -> failwith "Impossible!" in
          match uu____3993 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____4042 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____4042 t in
              let uu____4051 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____4051 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____4069 =
                       let uu____4070 = FStar_Syntax_Subst.compress t2 in
                       uu____4070.FStar_Syntax_Syntax.n in
                     match uu____4069 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4074) -> ibs
                     | uu____4095 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____4104 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____4105 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4104 uu____4105 in
                   let ind1 =
                     let uu____4109 =
                       FStar_List.map
                         (fun uu____4126 ->
                            match uu____4126 with
                            | (bv, aq) ->
                                let uu____4145 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4145, aq)) bs2 in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu____4109
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____4149 =
                       FStar_List.map
                         (fun uu____4166 ->
                            match uu____4166 with
                            | (bv, aq) ->
                                let uu____4185 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4185, aq)) ibs1 in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4149
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____4189 =
                       let uu____4190 = FStar_Syntax_Syntax.as_arg ind2 in
                       [uu____4190] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu____4189 FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____4239 =
                            let uu____4240 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____4240 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4239) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____4253 =
                              let uu____4256 =
                                let uu____4257 =
                                  let uu____4266 =
                                    FStar_Syntax_Syntax.bv_to_name
                                      (FStar_Pervasives_Native.fst b) in
                                  FStar_Syntax_Syntax.as_arg uu____4266 in
                                [uu____4257] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq uu____4256
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____4253)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___674_4289 = fml in
                     let uu____4290 =
                       let uu____4291 =
                         let uu____4298 =
                           let uu____4299 =
                             let uu____4320 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu____4325 =
                               let uu____4338 =
                                 let uu____4349 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____4349] in
                               [uu____4338] in
                             (uu____4320, uu____4325) in
                           FStar_Syntax_Syntax.Meta_pattern uu____4299 in
                         (fml, uu____4298) in
                       FStar_Syntax_Syntax.Tm_meta uu____4291 in
                     {
                       FStar_Syntax_Syntax.n = uu____4290;
                       FStar_Syntax_Syntax.pos =
                         (uu___674_4289.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___674_4289.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4418 =
                              let uu____4419 =
                                let uu____4428 =
                                  let uu____4429 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4429 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4428 in
                              [uu____4419] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4418
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4482 =
                              let uu____4483 =
                                let uu____4492 =
                                  let uu____4493 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4493 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4492 in
                              [uu____4483] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4482
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
          let uu____4567 =
            let uu____4568 = FStar_Syntax_Subst.compress dt1 in
            uu____4568.FStar_Syntax_Syntax.n in
          match uu____4567 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4572) ->
              let dbs1 =
                let uu____4602 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4602 in
              let dbs2 =
                let uu____4652 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4652 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4665 =
                           let uu____4666 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           [uu____4666] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____4665
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4697 =
                           let uu____4698 = FStar_Ident.string_of_lid ty_lid in
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             uu____4698 in
                         FStar_TypeChecker_Util.label uu____4697 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4704 =
                       let uu____4705 =
                         let uu____4714 =
                           let uu____4715 = FStar_Syntax_Subst.close [b] t in
                           FStar_Syntax_Util.abs
                             [((FStar_Pervasives_Native.fst b),
                                FStar_Pervasives_Native.None)] uu____4715
                             FStar_Pervasives_Native.None in
                         FStar_Syntax_Syntax.as_arg uu____4714 in
                       [uu____4705] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu____4704 FStar_Range.dummyRange) dbs3 cond
          | uu____4762 -> FStar_Syntax_Util.t_true
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
                  (lid, uu____4852, uu____4853, uu____4854, uu____4855,
                   uu____4856)
                  -> lid
              | uu____4865 -> failwith "Impossible!" in
            let uu____4866 = acc in
            match uu____4866 with
            | (uu____4903, en, uu____4905, uu____4906) ->
                let uu____4927 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____4927 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____4964 = acc in
                     (match uu____4964 with
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
                                     (uu____5038, uu____5039, uu____5040,
                                      t_lid, uu____5042, uu____5043)
                                     -> t_lid = lid
                                 | uu____5048 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5061 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5061)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5064 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5067 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5064, uu____5067)))
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
          let uu____5124 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5134, us, uu____5136, t, uu____5138, uu____5139) ->
                (us, t)
            | uu____5148 -> failwith "Impossible!" in
          match uu____5124 with
          | (us, t) ->
              let uu____5157 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____5157 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     let uu____5182 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu____5182 with
                     | (axioms, env2, guard, cond) ->
                         let phi =
                           let uu____5260 = FStar_Syntax_Util.arrow_formals t in
                           match uu____5260 with
                           | (uu____5267, t1) ->
                               let uu____5273 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu____5273
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu____5275 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                         (match uu____5275 with
                          | (phi1, uu____5283) ->
                              ((let uu____5285 =
                                  FStar_TypeChecker_Env.should_verify env2 in
                                if uu____5285
                                then
                                  let uu____5286 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5286
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l ->
                                       fun uu____5303 ->
                                         match uu____5303 with
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
                let uu____5371 =
                  let uu____5372 = FStar_Syntax_Subst.compress t in
                  uu____5372.FStar_Syntax_Syntax.n in
                match uu____5371 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5379) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5416 = is_mutual t' in
                    if uu____5416
                    then true
                    else
                      (let uu____5418 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5418)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5438) ->
                    is_mutual t'
                | uu____5443 -> false
              and exists_mutual uu___1_5444 =
                match uu___1_5444 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5463 =
                let uu____5464 = FStar_Syntax_Subst.compress dt1 in
                uu____5464.FStar_Syntax_Syntax.n in
              match uu____5463 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5470) ->
                  let dbs1 =
                    let uu____5500 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5500 in
                  let dbs2 =
                    let uu____5550 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5550 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5568 =
                               let uu____5569 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                               [uu____5569] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.t_haseq uu____5568
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5599 = is_mutual sort in
                             if uu____5599
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5609 =
                             let uu____5610 =
                               let uu____5619 =
                                 let uu____5620 =
                                   FStar_Syntax_Subst.close [b] t in
                                 FStar_Syntax_Util.abs
                                   [((FStar_Pervasives_Native.fst b),
                                      FStar_Pervasives_Native.None)]
                                   uu____5620 FStar_Pervasives_Native.None in
                               FStar_Syntax_Syntax.as_arg uu____5619 in
                             [uu____5610] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.tforall uu____5609
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5667 -> acc
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
              let uu____5716 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____5738, bs, t, uu____5741, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5753 -> failwith "Impossible!" in
              match uu____5716 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____5776 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____5776 t in
                  let uu____5785 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____5785 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____5795 =
                           let uu____5796 = FStar_Syntax_Subst.compress t2 in
                           uu____5796.FStar_Syntax_Syntax.n in
                         match uu____5795 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5800) ->
                             ibs
                         | uu____5821 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____5830 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____5831 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5830
                           uu____5831 in
                       let ind1 =
                         let uu____5835 =
                           FStar_List.map
                             (fun uu____5852 ->
                                match uu____5852 with
                                | (bv, aq) ->
                                    let uu____5871 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5871, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____5835
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____5875 =
                           FStar_List.map
                             (fun uu____5892 ->
                                match uu____5892 with
                                | (bv, aq) ->
                                    let uu____5911 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5911, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5875
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____5915 =
                           let uu____5916 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____5916] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____5915
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5952, uu____5953, uu____5954, t_lid,
                                   uu____5956, uu____5957)
                                  -> t_lid = lid
                              | uu____5962 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___911_5972 = fml in
                         let uu____5973 =
                           let uu____5974 =
                             let uu____5981 =
                               let uu____5982 =
                                 let uu____6003 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu____6008 =
                                   let uu____6021 =
                                     let uu____6032 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu____6032] in
                                   [uu____6021] in
                                 (uu____6003, uu____6008) in
                               FStar_Syntax_Syntax.Meta_pattern uu____5982 in
                             (fml, uu____5981) in
                           FStar_Syntax_Syntax.Tm_meta uu____5974 in
                         {
                           FStar_Syntax_Syntax.n = uu____5973;
                           FStar_Syntax_Syntax.pos =
                             (uu___911_5972.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___911_5972.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6101 =
                                  let uu____6102 =
                                    let uu____6111 =
                                      let uu____6112 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6112
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6111 in
                                  [uu____6102] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6101
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6165 =
                                  let uu____6166 =
                                    let uu____6175 =
                                      let uu____6176 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6176
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6175 in
                                  [uu____6166] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6165
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
                     (lid, uu____6267, uu____6268, uu____6269, uu____6270,
                      uu____6271)
                     -> lid
                 | uu____6280 -> failwith "Impossible!") tcs in
          let uu____6281 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6293, uu____6294, uu____6295, uu____6296) ->
                (lid, us)
            | uu____6305 -> failwith "Impossible!" in
          match uu____6281 with
          | (lid, us) ->
              let uu____6314 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6314 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6341 =
                       let uu____6342 =
                         let uu____6349 = get_haseq_axiom_lid lid in
                         (uu____6349, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6342 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6341;
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
          let uu____6402 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6428 ->
                    match uu___2_6428 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6429;
                        FStar_Syntax_Syntax.sigrng = uu____6430;
                        FStar_Syntax_Syntax.sigquals = uu____6431;
                        FStar_Syntax_Syntax.sigmeta = uu____6432;
                        FStar_Syntax_Syntax.sigattrs = uu____6433;
                        FStar_Syntax_Syntax.sigopts = uu____6434;_} -> true
                    | uu____6457 -> false)) in
          match uu____6402 with
          | (tys, datas) ->
              ((let uu____6479 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6489 ->
                          match uu___3_6489 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6490;
                              FStar_Syntax_Syntax.sigrng = uu____6491;
                              FStar_Syntax_Syntax.sigquals = uu____6492;
                              FStar_Syntax_Syntax.sigmeta = uu____6493;
                              FStar_Syntax_Syntax.sigattrs = uu____6494;
                              FStar_Syntax_Syntax.sigopts = uu____6495;_} ->
                              false
                          | uu____6516 -> true)) in
                if uu____6479
                then
                  let uu____6517 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6517
                else ());
               (let univs =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6525 =
                       let uu____6526 = FStar_List.hd tys in
                       uu____6526.FStar_Syntax_Syntax.sigel in
                     match uu____6525 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6529, uvs, uu____6531, uu____6532,
                          uu____6533, uu____6534)
                         -> uvs
                     | uu____6543 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6547 =
                  FStar_List.fold_right
                    (fun tc ->
                       fun uu____6586 ->
                         match uu____6586 with
                         | (env1, all_tcs, g) ->
                             let uu____6626 = tc_tycon env1 tc in
                             (match uu____6626 with
                              | (env2, tc1, tc_u, guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____6653 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____6653
                                    then
                                      let uu____6654 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____6654
                                    else ());
                                   (let uu____6656 =
                                      let uu____6657 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6657 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____6656))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard) in
                match uu____6547 with
                | (env1, tcs, g) ->
                    let uu____6703 =
                      FStar_List.fold_right
                        (fun se ->
                           fun uu____6725 ->
                             match uu____6725 with
                             | (datas1, g1) ->
                                 let uu____6744 =
                                   let uu____6749 = tc_data env1 tcs in
                                   uu____6749 se in
                                 (match uu____6744 with
                                  | (data, g') ->
                                      let uu____6766 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____6766))) datas
                        ([], g) in
                    (match uu____6703 with
                     | (datas1, g1) ->
                         let uu____6787 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             let uu___1022_6804 = g1 in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1022_6804.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (uu___1022_6804.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1022_6804.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1022_6804.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu____6814 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu____6814
                            then
                              let uu____6815 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____6815
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____6827 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs in
                              (uu____6827, datas1)) in
                         (match uu____6787 with
                          | (tcs1, datas2) ->
                              let sig_bndle =
                                let uu____6859 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____6860 =
                                  FStar_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____6859;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____6860;
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
                                            uu____6886, uu____6887)
                                           ->
                                           let fail expected inferred =
                                             let uu____6907 =
                                               let uu____6912 =
                                                 let uu____6913 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu____6914 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____6913 uu____6914 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____6912) in
                                             FStar_Errors.raise_error
                                               uu____6907
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu____6915 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____6915 with
                                            | FStar_Pervasives_Native.None ->
                                                ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ, uu____6931) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____6962 ->
                                                        let uu____6963 =
                                                          let uu____6964 =
                                                            let uu____6979 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                typ in
                                                            (binders,
                                                              uu____6979) in
                                                          FStar_Syntax_Syntax.Tm_arrow
                                                            uu____6964 in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____6963
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs1, body) in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ))
                                                then
                                                  let uu____7000 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____7000 with
                                                   | (uu____7005, inferred)
                                                       ->
                                                       let uu____7007 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ in
                                                       (match uu____7007 with
                                                        | (uu____7012,
                                                           expected) ->
                                                            let uu____7014 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected in
                                                            if uu____7014
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ
                                                                inferred_typ))
                                                else
                                                  fail expected_typ
                                                    inferred_typ)
                                       | uu____7017 -> ()));
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
                              let uu____7121 =
                                let uu____7122 =
                                  let uu____7129 =
                                    let uu____7132 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7132 in
                                  (uu____7129, inst_univs) in
                                FStar_Syntax_Syntax.Tm_uinst uu____7122 in
                              FStar_Syntax_Syntax.mk uu____7121 p in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7166 ->
                                      match uu____7166 with
                                      | (x, imp) ->
                                          let uu____7185 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____7185, imp))) in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args p in
                          let unrefined_arg_binder =
                            let uu____7189 = projectee arg_typ in
                            FStar_Syntax_Syntax.mk_binder uu____7189 in
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
                                   let uu____7210 =
                                     FStar_Ident.set_lid_range disc_name p in
                                   FStar_Syntax_Syntax.fvar uu____7210
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None in
                                 let uu____7211 =
                                   let uu____7214 =
                                     let uu____7217 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs in
                                     let uu____7218 =
                                       let uu____7219 =
                                         let uu____7228 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7228 in
                                       [uu____7219] in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7217
                                       uu____7218 p in
                                   FStar_Syntax_Util.b2t uu____7214 in
                                 FStar_Syntax_Util.refine x uu____7211 in
                               let uu____7253 =
                                 let uu___1097_7254 = projectee arg_typ in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1097_7254.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1097_7254.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 } in
                               FStar_Syntax_Syntax.mk_binder uu____7253) in
                          let ntps = FStar_List.length tps in
                          let all_params =
                            let uu____7271 =
                              FStar_List.map
                                (fun uu____7295 ->
                                   match uu____7295 with
                                   | (x, uu____7309) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps in
                            FStar_List.append uu____7271 fields in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7368 ->
                                    match uu____7368 with
                                    | (x, uu____7382) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)))) in
                          let early_prims_inductive =
                            (let uu____7392 =
                               FStar_TypeChecker_Env.current_module env in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7392)
                              &&
                              (FStar_List.existsb
                                 (fun s ->
                                    let uu____7396 =
                                      let uu____7397 =
                                        FStar_Ident.ident_of_lid tc in
                                      FStar_Ident.string_of_id uu____7397 in
                                    s = uu____7396) early_prims_inductives) in
                          let discriminator_ses =
                            if fvq <> FStar_Syntax_Syntax.Data_ctor
                            then []
                            else
                              (let discriminator_name =
                                 FStar_Syntax_Util.mk_discriminator lid in
                               let no_decl = false in
                               let only_decl =
                                 early_prims_inductive ||
                                   (let uu____7408 =
                                      let uu____7409 =
                                        FStar_TypeChecker_Env.current_module
                                          env in
                                      FStar_Ident.string_of_lid uu____7409 in
                                    FStar_Options.dont_gen_projectors
                                      uu____7408) in
                               let quals =
                                 let uu____7413 =
                                   FStar_List.filter
                                     (fun uu___4_7417 ->
                                        match uu___4_7417 with
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                            -> true
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu____7418 -> false) iquals in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____7413 in
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
                                 let uu____7458 =
                                   FStar_Syntax_Util.arrow binders bool_typ in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____7458 in
                               let decl =
                                 let uu____7462 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____7462;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               (let uu____7464 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes") in
                                if uu____7464
                                then
                                  let uu____7465 =
                                    FStar_Syntax_Print.sigelt_to_string decl in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____7465
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
                                                 fun uu____7516 ->
                                                   match uu____7516 with
                                                   | (x, imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____7536 =
                                                           let uu____7539 =
                                                             let uu____7540 =
                                                               let uu____7547
                                                                 =
                                                                 let uu____7548
                                                                   =
                                                                   FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   uu____7548
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun in
                                                               (uu____7547,
                                                                 FStar_Syntax_Syntax.tun) in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____7540 in
                                                           pos uu____7539 in
                                                         (uu____7536, b)
                                                       else
                                                         (let uu____7554 =
                                                            let uu____7557 =
                                                              let uu____7558
                                                                =
                                                                let uu____7559
                                                                  =
                                                                  FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  uu____7559
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____7558 in
                                                            pos uu____7557 in
                                                          (uu____7554, b)))) in
                                       let pat_true =
                                         let uu____7577 =
                                           let uu____7580 =
                                             let uu____7581 =
                                               let uu____7594 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq) in
                                               (uu____7594, arg_pats) in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____7581 in
                                           pos uu____7580 in
                                         (uu____7577,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool) in
                                       let pat_false =
                                         let uu____7628 =
                                           let uu____7631 =
                                             let uu____7632 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____7632 in
                                           pos uu____7631 in
                                         (uu____7628,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool) in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder) in
                                       let uu____7646 =
                                         let uu____7647 =
                                           let uu____7670 =
                                             let uu____7687 =
                                               FStar_Syntax_Util.branch
                                                 pat_true in
                                             let uu____7702 =
                                               let uu____7719 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false in
                                               [uu____7719] in
                                             uu____7687 :: uu____7702 in
                                           (arg_exp, uu____7670) in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____7647 in
                                       FStar_Syntax_Syntax.mk uu____7646 p) in
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
                                    let uu____7805 =
                                      let uu____7810 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None in
                                      FStar_Util.Inr uu____7810 in
                                    let uu____7811 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____7805 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____7811 [] FStar_Range.dummyRange in
                                  let impl =
                                    let uu____7817 =
                                      let uu____7818 =
                                        let uu____7825 =
                                          let uu____7828 =
                                            let uu____7829 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right in
                                            FStar_All.pipe_right uu____7829
                                              (fun fv ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                          [uu____7828] in
                                        ((false, [lb]), uu____7825) in
                                      FStar_Syntax_Syntax.Sig_let uu____7818 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____7817;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    } in
                                  (let uu____7841 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes") in
                                   if uu____7841
                                   then
                                     let uu____7842 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____7842
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
                                    fun uu____7910 ->
                                      match uu____7910 with
                                      | (a, uu____7918) ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i in
                                          let field_proj_tm =
                                            let uu____7925 =
                                              let uu____7926 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____7926 in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu____7925 inst_univs in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p in
                                          FStar_Syntax_Syntax.NT (a, proj))) in
                          let projectors_ses =
                            let uu____7949 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu____7989 ->
                                        match uu____7989 with
                                        | (x, uu____7999) ->
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
                                              let uu____8016 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu____8016 in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu____8021 =
                                                   let uu____8022 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env in
                                                   FStar_Ident.string_of_lid
                                                     uu____8022 in
                                                 FStar_Options.dont_gen_projectors
                                                   uu____8021) in
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
                                                     (fun uu___5_8050 ->
                                                        match uu___5_8050
                                                        with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                            -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                            -> true
                                                        | FStar_Syntax_Syntax.Private
                                                            -> true
                                                        | uu____8051 -> false)) in
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
                                              let uu____8059 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu____8059;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu____8061 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes") in
                                              if uu____8061
                                              then
                                                let uu____8062 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu____8062
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu____8068 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu____8068
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_All.pipe_right
                                                    all_params
                                                    (FStar_List.mapi
                                                       (fun j ->
                                                          fun uu____8109 ->
                                                            match uu____8109
                                                            with
                                                            | (x1, imp) ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu____8129
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                  (uu____8129,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____8141
                                                                    =
                                                                    let uu____8144
                                                                    =
                                                                    let uu____8145
                                                                    =
                                                                    let uu____8152
                                                                    =
                                                                    let uu____8153
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8153
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8152,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8145 in
                                                                    pos
                                                                    uu____8144 in
                                                                    (uu____8141,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____8159
                                                                    =
                                                                    let uu____8162
                                                                    =
                                                                    let uu____8163
                                                                    =
                                                                    let uu____8164
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8164
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8163 in
                                                                    pos
                                                                    uu____8162 in
                                                                    (uu____8159,
                                                                    b)))) in
                                                let pat =
                                                  let uu____8182 =
                                                    let uu____8185 =
                                                      let uu____8186 =
                                                        let uu____8199 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu____8199,
                                                          arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____8186 in
                                                    pos uu____8185 in
                                                  let uu____8208 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu____8182,
                                                    FStar_Pervasives_Native.None,
                                                    uu____8208) in
                                                let body =
                                                  let uu____8224 =
                                                    let uu____8225 =
                                                      let uu____8248 =
                                                        let uu____8265 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu____8265] in
                                                      (arg_exp, uu____8248) in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu____8225 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____8224 p1 in
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
                                                  let uu____8337 =
                                                    let uu____8342 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Util.Inr uu____8342 in
                                                  let uu____8343 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____8337;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____8343;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  } in
                                                let impl =
                                                  let uu____8349 =
                                                    let uu____8350 =
                                                      let uu____8357 =
                                                        let uu____8360 =
                                                          let uu____8361 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right in
                                                          FStar_All.pipe_right
                                                            uu____8361
                                                            (fun fv ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [uu____8360] in
                                                      ((false, [lb]),
                                                        uu____8357) in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____8350 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____8349;
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
                                                (let uu____8373 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes") in
                                                 if uu____8373
                                                 then
                                                   let uu____8374 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu____8374
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl])))) in
                            FStar_All.pipe_right uu____7949
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
                (constr_lid, uvs, t, typ_lid, n_typars, uu____8431) when
                let uu____8436 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid in
                Prims.op_Negation uu____8436 ->
                let uu____8437 = FStar_Syntax_Subst.univ_var_opening uvs in
                (match uu____8437 with
                 | (univ_opening, uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t in
                     let uu____8459 = FStar_Syntax_Util.arrow_formals t1 in
                     (match uu____8459 with
                      | (formals, uu____8469) ->
                          let uu____8474 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1 ->
                                   let uu____8506 =
                                     let uu____8507 =
                                       let uu____8508 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____8508 in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____8507 in
                                   if uu____8506
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____8527, uvs', tps, typ0,
                                          uu____8531, constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____8548 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None) in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                let uu____8589 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid in
                                if uu____8589
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng in
                          (match uu____8474 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0 in
                               let uu____8616 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu____8616 with
                                | (indices, uu____8626) ->
                                    let refine_domain =
                                      let uu____8632 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___6_8637 ->
                                                match uu___6_8637 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____8638 -> true
                                                | uu____8647 -> false)) in
                                      if uu____8632
                                      then false
                                      else should_refine in
                                    let fv_qual =
                                      let filter_records uu___7_8657 =
                                        match uu___7_8657 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____8660, fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu____8672 ->
                                            FStar_Pervasives_Native.None in
                                      let uu____8673 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu____8673 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu____8678 =
                                        FStar_Util.first_N n_typars formals in
                                      match uu____8678 with
                                      | (imp_tps, fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____8761 ->
                                                 fun uu____8762 ->
                                                   match (uu____8761,
                                                           uu____8762)
                                                   with
                                                   | ((x, uu____8788),
                                                      (x', uu____8790)) ->
                                                       let uu____8811 =
                                                         let uu____8818 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu____8818) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____8811) imp_tps
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
            | uu____8824 -> []