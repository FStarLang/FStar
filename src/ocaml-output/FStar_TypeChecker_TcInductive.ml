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
                                             FStar_Syntax_Util.head_and_args
                                               result1 in
                                           (match uu____1031 with
                                            | (head, args) ->
                                                let p_args =
                                                  let uu____1089 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1089 in
                                                (FStar_List.iter2
                                                   (fun uu____1171 ->
                                                      fun uu____1172 ->
                                                        match (uu____1171,
                                                                uu____1172)
                                                        with
                                                        | ((bv, uu____1202),
                                                           (t2, uu____1204))
                                                            ->
                                                            let uu____1231 =
                                                              let uu____1232
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2 in
                                                              uu____1232.FStar_Syntax_Syntax.n in
                                                            (match uu____1231
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1236 ->
                                                                 let uu____1237
                                                                   =
                                                                   let uu____1242
                                                                    =
                                                                    let uu____1243
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv in
                                                                    let uu____1244
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1243
                                                                    uu____1244 in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1242) in
                                                                 FStar_Errors.raise_error
                                                                   uu____1237
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1246 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ in
                                                    FStar_All.pipe_right
                                                      uu____1246
                                                      FStar_Syntax_Util.unrefine in
                                                  (let uu____1248 =
                                                     let uu____1249 =
                                                       FStar_Syntax_Subst.compress
                                                         ty in
                                                     uu____1249.FStar_Syntax_Syntax.n in
                                                   match uu____1248 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1252 -> ()
                                                   | uu____1253 ->
                                                       let uu____1254 =
                                                         let uu____1259 =
                                                           let uu____1260 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1 in
                                                           let uu____1261 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1260
                                                             uu____1261 in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1259) in
                                                       FStar_Errors.raise_error
                                                         uu____1254
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1263 =
                                                       let uu____1264 =
                                                         FStar_Syntax_Subst.compress
                                                           head in
                                                       uu____1264.FStar_Syntax_Syntax.n in
                                                     match uu____1263 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1268;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1269;_},
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
                                                                    let uu____1282
                                                                    =
                                                                    let uu____1283
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Range.dummyRange in
                                                                    let uu____1284
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____1283
                                                                    uu____1284 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1282)
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
                                                     | uu____1287 ->
                                                         let uu____1288 =
                                                           let uu____1293 =
                                                             let uu____1294 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid in
                                                             let uu____1295 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1294
                                                               uu____1295 in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1293) in
                                                         FStar_Errors.raise_error
                                                           uu____1288
                                                           se.FStar_Syntax_Syntax.sigrng in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g ->
                                                          fun uu____1310 ->
                                                            fun u_x ->
                                                              match uu____1310
                                                              with
                                                              | (x,
                                                                 uu____1319)
                                                                  ->
                                                                  let uu____1324
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1324)
                                                       g_uvs arguments1 us in
                                                   let t2 =
                                                     let uu____1328 =
                                                       let uu____1337 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1377
                                                                 ->
                                                                 match uu____1377
                                                                 with
                                                                 | (x,
                                                                    uu____1391)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                       FStar_List.append
                                                         uu____1337
                                                         arguments1 in
                                                     let uu____1404 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1 in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1328 uu____1404 in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2 in
                                                   ((let uu___189_1409 = se in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___189_1409.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___189_1409.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___189_1409.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___189_1409.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___189_1409.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1412 -> failwith "impossible"
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
               (fun uu____1501 ->
                  match uu____1501 with
                  | (se, uu____1507) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1508, uu____1509, tps, k, uu____1512,
                            uu____1513)
                           ->
                           let uu____1522 =
                             let uu____1523 = FStar_Syntax_Syntax.mk_Total k in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1523 in
                           FStar_Syntax_Syntax.null_binder uu____1522
                       | uu____1528 -> failwith "Impossible"))) in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1556, uu____1557, t, uu____1559, uu____1560,
                       uu____1561)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1566 -> failwith "Impossible")) in
        let t =
          let uu____1570 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1570 in
        (let uu____1580 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses") in
         if uu____1580
         then
           let uu____1581 = FStar_TypeChecker_Normalize.term_to_string env t in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1581
         else ());
        (let uu____1583 =
           FStar_TypeChecker_Generalize.generalize_universes env t in
         match uu____1583 with
         | (uvs, t1) ->
             ((let uu____1603 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses") in
               if uu____1603
               then
                 let uu____1604 =
                   let uu____1605 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u -> FStar_Ident.string_of_id u)) in
                   FStar_All.pipe_right uu____1605 (FStar_String.concat ", ") in
                 let uu____1616 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1604 uu____1616
               else ());
              (let uu____1618 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
               match uu____1618 with
               | (uvs1, t2) ->
                   let uu____1633 = FStar_Syntax_Util.arrow_formals t2 in
                   (match uu____1633 with
                    | (args, uu____1649) ->
                        let uu____1654 =
                          FStar_Util.first_N (FStar_List.length binders) args in
                        (match uu____1654 with
                         | (tc_types, data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1759 ->
                                    fun uu____1760 ->
                                      match (uu____1759, uu____1760) with
                                      | ((x, uu____1782), (se, uu____1784))
                                          ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc, uu____1800, tps,
                                                uu____1802, mutuals, datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort in
                                               let uu____1814 =
                                                 let uu____1819 =
                                                   let uu____1820 =
                                                     FStar_Syntax_Subst.compress
                                                       ty in
                                                   uu____1820.FStar_Syntax_Syntax.n in
                                                 match uu____1819 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1, c) ->
                                                     let uu____1849 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1 in
                                                     (match uu____1849 with
                                                      | (tps1, rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____1927 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                          (tps1, t3))
                                                 | uu____1946 -> ([], ty) in
                                               (match uu____1814 with
                                                | (tps1, t3) ->
                                                    let uu___266_1955 = se in
                                                    {
                                                      FStar_Syntax_Syntax.sigel
                                                        =
                                                        (FStar_Syntax_Syntax.Sig_inductive_typ
                                                           (tc, uvs1, tps1,
                                                             t3, mutuals,
                                                             datas1));
                                                      FStar_Syntax_Syntax.sigrng
                                                        =
                                                        (uu___266_1955.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___266_1955.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___266_1955.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___266_1955.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___266_1955.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____1960 ->
                                               failwith "Impossible"))
                                 tc_types tcs in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____1966 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun uu____1970 ->
                                             FStar_Syntax_Syntax.U_name
                                               uu____1970)) in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_1990 ->
                                             match uu___0_1990 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc, uu____1996,
                                                    uu____1997, uu____1998,
                                                    uu____1999, uu____2000);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2001;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2002;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2003;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2004;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2005;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2020 ->
                                                 failwith "Impossible")) in
                                   FStar_List.map2
                                     (fun uu____2043 ->
                                        fun d ->
                                          match uu____2043 with
                                          | (t3, uu____2052) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l, uu____2058,
                                                    uu____2059, tc, ntps,
                                                    mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2068 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort in
                                                     FStar_All.pipe_right
                                                       uu____2068
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1) in
                                                   let uu___303_2069 = d in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___303_2069.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___303_2069.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___303_2069.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___303_2069.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___303_2069.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2072 ->
                                                   failwith "Impossible"))
                                     data_types datas in
                             (tcs1, datas1))))))
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env ->
    fun msg ->
      let uu____2092 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____2092
      then
        let uu____2093 =
          let uu____2094 =
            let uu____2095 = msg () in Prims.op_Hat uu____2095 "\n" in
          Prims.op_Hat "Positivity::" uu____2094 in
        FStar_Util.print_string uu____2093
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____2107 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____2107
let rec (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____2127 =
      let uu____2128 = FStar_Syntax_Subst.compress t in
      uu____2128.FStar_Syntax_Syntax.n in
    match uu____2127 with
    | FStar_Syntax_Syntax.Tm_name uu____2137 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives_Native.Some (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu____2153 =
          let uu____2154 = FStar_Syntax_Subst.compress t1 in
          uu____2154.FStar_Syntax_Syntax.n in
        (match uu____2153 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, us)
         | uu____2168 ->
             failwith
               "try_get_fv: Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2176, uu____2177) ->
        try_get_fv t1
    | uu____2218 ->
        let uu____2219 =
          let uu____2220 = FStar_Syntax_Print.tag_of_term t in
          Prims.op_Hat "try_get_fv: did not expect t to be a : " uu____2220 in
        failwith uu____2219
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
          let uu____2255 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2291 ->
               match uu____2291 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2334 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2334 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2255
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
            (fun uu____2530 ->
               let uu____2531 = FStar_Syntax_Print.term_to_string btype in
               Prims.op_Hat "Checking strict positivity in type: " uu____2531);
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
             (fun uu____2536 ->
                let uu____2537 = FStar_Syntax_Print.term_to_string btype1 in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2537);
           (let uu____2540 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2540) ||
             ((debug_log env
                 (fun uu____2549 ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2550 =
                  let uu____2551 = FStar_Syntax_Subst.compress btype1 in
                  uu____2551.FStar_Syntax_Syntax.n in
                match uu____2550 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let fv_us_opt = try_get_fv t in
                    let uu____2587 =
                      FStar_All.pipe_right fv_us_opt FStar_Util.is_none in
                    if uu____2587
                    then true
                    else
                      (let uu____2599 =
                         FStar_All.pipe_right fv_us_opt FStar_Util.must in
                       match uu____2599 with
                       | (fv, us) ->
                           let uu____2620 =
                             FStar_Ident.lid_equals
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               ty_lid in
                           if uu____2620
                           then
                             (debug_log env
                                (fun uu____2623 ->
                                   "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                              FStar_List.for_all
                                (fun uu____2634 ->
                                   match uu____2634 with
                                   | (t1, uu____2642) ->
                                       let uu____2647 =
                                         ty_occurs_in ty_lid t1 in
                                       Prims.op_Negation uu____2647) args)
                           else
                             (debug_log env
                                (fun uu____2651 ->
                                   "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                              ty_nested_positive_in_inductive ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env
                       (fun uu____2676 ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp =
                        let c1 =
                          let uu____2681 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu____2681
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2685 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu____2685
                             (FStar_List.existsb
                                (fun q -> q = FStar_Syntax_Syntax.TotalEffect))) in
                      if Prims.op_Negation check_comp
                      then
                        (debug_log env
                           (fun uu____2694 ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2698 ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2709 ->
                               match uu____2709 with
                               | (b, uu____2717) ->
                                   let uu____2722 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2722) sbs)
                           &&
                           ((let uu____2727 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2727 with
                             | (uu____2732, return_type) ->
                                 let uu____2734 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2734)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2735 ->
                    (debug_log env
                       (fun uu____2738 ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2739 ->
                    (debug_log env
                       (fun uu____2742 ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2744) ->
                    (debug_log env
                       (fun uu____2751 ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2753) ->
                    (debug_log env
                       (fun uu____2760 ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2761, branches) ->
                    (debug_log env
                       (fun uu____2801 ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2821 ->
                          match uu____2821 with
                          | (p, uu____2833, t) ->
                              let bs =
                                let uu____2852 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2852 in
                              let uu____2861 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2861 with
                               | (bs1, t1) ->
                                   let uu____2868 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2868)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2870, uu____2871)
                    ->
                    (debug_log env
                       (fun uu____2914 ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2915 ->
                    (debug_log env
                       (fun uu____2919 ->
                          let uu____2920 =
                            let uu____2921 =
                              FStar_Syntax_Print.tag_of_term btype1 in
                            let uu____2922 =
                              let uu____2923 =
                                FStar_Syntax_Print.term_to_string btype1 in
                              Prims.op_Hat " and term: " uu____2923 in
                            Prims.op_Hat uu____2921 uu____2922 in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____2920);
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
                (fun uu____2933 ->
                   let uu____2934 =
                     let uu____2935 = FStar_Ident.string_of_lid ilid in
                     let uu____2936 =
                       let uu____2937 =
                         FStar_Syntax_Print.args_to_string args in
                       Prims.op_Hat " applied to arguments: " uu____2937 in
                     Prims.op_Hat uu____2935 uu____2936 in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____2934);
              (let uu____2938 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2938 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2951 =
                       let uu____2952 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       FStar_TypeChecker_Env.fv_has_attr env uu____2952
                         FStar_Parser_Const.assume_strictly_positive_attr_lid in
                     (if uu____2951
                      then
                        (debug_log env
                           (fun uu____2956 ->
                              let uu____2957 = FStar_Ident.string_of_lid ilid in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____2957);
                         true)
                      else
                        (debug_log env
                           (fun uu____2961 ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____2963 =
                        already_unfolded ilid args unfolded env in
                      if uu____2963
                      then
                        (debug_log env
                           (fun uu____2966 ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____2969 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu____2969 in
                         debug_log env
                           (fun uu____2975 ->
                              let uu____2976 =
                                let uu____2977 =
                                  FStar_Util.string_of_int num_ibs in
                                Prims.op_Hat uu____2977
                                  ", also adding to the memo table" in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____2976);
                         (let uu____2979 =
                            let uu____2980 = FStar_ST.op_Bang unfolded in
                            let uu____2993 =
                              let uu____3000 =
                                let uu____3005 =
                                  let uu____3006 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3006 in
                                (ilid, uu____3005) in
                              [uu____3000] in
                            FStar_List.append uu____2980 uu____2993 in
                          FStar_ST.op_Colon_Equals unfolded uu____2979);
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
                    (fun uu____3090 ->
                       let uu____3091 =
                         let uu____3092 = FStar_Ident.string_of_lid dlid in
                         let uu____3093 =
                           let uu____3094 = FStar_Ident.string_of_lid ilid in
                           Prims.op_Hat " of the inductive " uu____3094 in
                         Prims.op_Hat uu____3092 uu____3093 in
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         uu____3091);
                  (let uu____3095 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3095 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3119 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        debug_log env
                          (fun uu____3123 ->
                             let uu____3124 =
                               FStar_Syntax_Print.term_to_string dt in
                             Prims.op_Hat
                               "Checking nested positivity in the data constructor type: "
                               uu____3124);
                        (let uu____3125 =
                           let uu____3126 = FStar_Syntax_Subst.compress dt in
                           uu____3126.FStar_Syntax_Syntax.n in
                         match uu____3125 with
                         | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                             (debug_log env
                                (fun uu____3153 ->
                                   "Checked nested positivity in Tm_arrow data constructor type");
                              (let uu____3154 =
                                 FStar_List.splitAt num_ibs dbs in
                               match uu____3154 with
                               | (ibs, dbs1) ->
                                   let ibs1 =
                                     FStar_Syntax_Subst.open_binders ibs in
                                   let dbs2 =
                                     let uu____3217 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_binders
                                       uu____3217 dbs1 in
                                   let c1 =
                                     let uu____3221 =
                                       FStar_Syntax_Subst.opening_of_binders
                                         ibs1 in
                                     FStar_Syntax_Subst.subst_comp uu____3221
                                       c in
                                   let uu____3224 =
                                     FStar_List.splitAt num_ibs args in
                                   (match uu____3224 with
                                    | (args1, uu____3258) ->
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
                                          let uu____3350 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length dbs3) subst in
                                          FStar_Syntax_Subst.subst_comp
                                            uu____3350 c1 in
                                        (debug_log env
                                           (fun uu____3362 ->
                                              let uu____3363 =
                                                let uu____3364 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    "; " dbs3 in
                                                let uu____3365 =
                                                  let uu____3366 =
                                                    FStar_Syntax_Print.comp_to_string
                                                      c2 in
                                                  Prims.op_Hat ", and c: "
                                                    uu____3366 in
                                                Prims.op_Hat uu____3364
                                                  uu____3365 in
                                              Prims.op_Hat
                                                "Checking nested positivity in the unfolded data constructor binders as: "
                                                uu____3363);
                                         ty_nested_positive_in_type ty_lid
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (dbs3, c2)) ilid num_ibs
                                           unfolded env))))
                         | uu____3377 ->
                             (debug_log env
                                (fun uu____3380 ->
                                   "Checking nested positivity in the data constructor type that is not an arrow");
                              (let uu____3381 =
                                 let uu____3382 =
                                   FStar_Syntax_Subst.compress dt in
                                 uu____3382.FStar_Syntax_Syntax.n in
                               ty_nested_positive_in_type ty_lid uu____3381
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
                     (fun uu____3419 ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3420 =
                      let uu____3425 = try_get_fv t1 in
                      FStar_All.pipe_right uu____3425 FStar_Util.must in
                    match uu____3420 with
                    | (fv, uu____3447) ->
                        let uu____3448 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____3448
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  (debug_log env
                     (fun uu____3475 ->
                        let uu____3476 =
                          FStar_Syntax_Print.binders_to_string "; " sbs in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3476);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3478 =
                      FStar_List.fold_left
                        (fun uu____3497 ->
                           fun b ->
                             match uu____3497 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3520 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3523 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3520, uu____3523))) (true, env)
                        sbs1 in
                    match uu____3478 with | (b, uu____3537) -> b))
              | uu____3538 ->
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
              let uu____3569 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3569 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3593 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3597 ->
                        let uu____3598 = FStar_Syntax_Print.term_to_string dt in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3598);
                   (let uu____3599 =
                      let uu____3600 = FStar_Syntax_Subst.compress dt in
                      uu____3600.FStar_Syntax_Syntax.n in
                    match uu____3599 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3603 ->
                        (debug_log env
                           (fun uu____3606 ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3608) ->
                        let dbs1 =
                          let uu____3638 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3638 in
                        let dbs2 =
                          let uu____3688 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3688 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        (debug_log env
                           (fun uu____3695 ->
                              let uu____3696 =
                                let uu____3697 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3) in
                                Prims.op_Hat uu____3697 " binders" in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3696);
                         (let uu____3704 =
                            FStar_List.fold_left
                              (fun uu____3723 ->
                                 fun b ->
                                   match uu____3723 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3746 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3749 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3746, uu____3749)))
                              (true, env) dbs3 in
                          match uu____3704 with | (b, uu____3763) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3764, uu____3765) ->
                        (debug_log env
                           (fun uu____3792 ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs) ->
                        (debug_log env
                           (fun uu____3801 ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3802 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3820 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____3836, uu____3837, uu____3838) ->
            (lid, us, bs)
        | uu____3847 -> failwith "Impossible!" in
      match uu____3820 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____3857 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3857 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3880 =
                 let uu____3883 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3883 in
               FStar_List.for_all
                 (fun d ->
                    let uu____3895 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3895
                      unfolded_inductives env2) uu____3880)
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
        (uu____3926, uu____3927, t, uu____3929, uu____3930, uu____3931) -> t
    | uu____3936 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = FStar_Ident.string_of_lid lid in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____3946 =
         let uu____3947 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____3947 haseq_suffix in
       uu____3946 = Prims.int_zero)
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____3953 =
      let uu____3954 = FStar_Ident.ns_of_lid lid in
      let uu____3957 =
        let uu____3960 =
          let uu____3961 =
            let uu____3962 =
              let uu____3963 = FStar_Ident.ident_of_lid lid in
              FStar_Ident.string_of_id uu____3963 in
            Prims.op_Hat uu____3962 haseq_suffix in
          FStar_Ident.id_of_text uu____3961 in
        [uu____3960] in
      FStar_List.append uu____3954 uu____3957 in
    FStar_Ident.lid_of_ids uu____3953
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
          let uu____4008 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4022, bs, t, uu____4025, uu____4026) ->
                (lid, bs, t)
            | uu____4035 -> failwith "Impossible!" in
          match uu____4008 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____4057 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____4057 t in
              let uu____4066 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____4066 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____4084 =
                       let uu____4085 = FStar_Syntax_Subst.compress t2 in
                       uu____4085.FStar_Syntax_Syntax.n in
                     match uu____4084 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4089) -> ibs
                     | uu____4110 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____4119 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____4120 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4119 uu____4120 in
                   let ind1 =
                     let uu____4124 =
                       FStar_List.map
                         (fun uu____4141 ->
                            match uu____4141 with
                            | (bv, aq) ->
                                let uu____4160 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4160, aq)) bs2 in
                     FStar_Syntax_Syntax.mk_Tm_app ind uu____4124
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____4164 =
                       FStar_List.map
                         (fun uu____4181 ->
                            match uu____4181 with
                            | (bv, aq) ->
                                let uu____4200 =
                                  FStar_Syntax_Syntax.bv_to_name bv in
                                (uu____4200, aq)) ibs1 in
                     FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4164
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____4204 =
                       let uu____4205 = FStar_Syntax_Syntax.as_arg ind2 in
                       [uu____4205] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                       uu____4204 FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____4254 =
                            let uu____4255 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____4255 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4254) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____4268 =
                              let uu____4271 =
                                let uu____4272 =
                                  let uu____4281 =
                                    FStar_Syntax_Syntax.bv_to_name
                                      (FStar_Pervasives_Native.fst b) in
                                  FStar_Syntax_Syntax.as_arg uu____4281 in
                                [uu____4272] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.t_haseq uu____4271
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____4268)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___677_4304 = fml in
                     let uu____4305 =
                       let uu____4306 =
                         let uu____4313 =
                           let uu____4314 =
                             let uu____4335 =
                               FStar_Syntax_Syntax.binders_to_names ibs1 in
                             let uu____4340 =
                               let uu____4353 =
                                 let uu____4364 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____4364] in
                               [uu____4353] in
                             (uu____4335, uu____4340) in
                           FStar_Syntax_Syntax.Meta_pattern uu____4314 in
                         (fml, uu____4313) in
                       FStar_Syntax_Syntax.Tm_meta uu____4306 in
                     {
                       FStar_Syntax_Syntax.n = uu____4305;
                       FStar_Syntax_Syntax.pos =
                         (uu___677_4304.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___677_4304.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4433 =
                              let uu____4434 =
                                let uu____4443 =
                                  let uu____4444 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4444 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4443 in
                              [uu____4434] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4433
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4497 =
                              let uu____4498 =
                                let uu____4507 =
                                  let uu____4508 =
                                    FStar_Syntax_Subst.close [b] t3 in
                                  FStar_Syntax_Util.abs
                                    [((FStar_Pervasives_Native.fst b),
                                       FStar_Pervasives_Native.None)]
                                    uu____4508 FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.as_arg uu____4507 in
                              [uu____4498] in
                            FStar_Syntax_Syntax.mk_Tm_app
                              FStar_Syntax_Util.tforall uu____4497
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
          let uu____4582 =
            let uu____4583 = FStar_Syntax_Subst.compress dt1 in
            uu____4583.FStar_Syntax_Syntax.n in
          match uu____4582 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4587) ->
              let dbs1 =
                let uu____4617 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4617 in
              let dbs2 =
                let uu____4667 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4667 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4680 =
                           let uu____4681 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           [uu____4681] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____4680
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4712 =
                           let uu____4713 = FStar_Ident.string_of_lid ty_lid in
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             uu____4713 in
                         FStar_TypeChecker_Util.label uu____4712 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4719 =
                       let uu____4720 =
                         let uu____4729 =
                           let uu____4730 = FStar_Syntax_Subst.close [b] t in
                           FStar_Syntax_Util.abs
                             [((FStar_Pervasives_Native.fst b),
                                FStar_Pervasives_Native.None)] uu____4730
                             FStar_Pervasives_Native.None in
                         FStar_Syntax_Syntax.as_arg uu____4729 in
                       [uu____4720] in
                     FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                       uu____4719 FStar_Range.dummyRange) dbs3 cond
          | uu____4777 -> FStar_Syntax_Util.t_true
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
                  (lid, uu____4867, uu____4868, uu____4869, uu____4870,
                   uu____4871)
                  -> lid
              | uu____4880 -> failwith "Impossible!" in
            let uu____4881 = acc in
            match uu____4881 with
            | (uu____4918, en, uu____4920, uu____4921) ->
                let uu____4942 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____4942 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____4979 = acc in
                     (match uu____4979 with
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
                                     (uu____5053, uu____5054, uu____5055,
                                      t_lid, uu____5057, uu____5058)
                                     -> t_lid = lid
                                 | uu____5063 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5076 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5076)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5079 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5082 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5079, uu____5082)))
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
          let uu____5139 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5149, us, uu____5151, t, uu____5153, uu____5154) ->
                (us, t)
            | uu____5163 -> failwith "Impossible!" in
          match uu____5139 with
          | (us, t) ->
              let uu____5172 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____5172 with
               | (usubst, us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     let uu____5197 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs in
                     match uu____5197 with
                     | (axioms, env2, guard, cond) ->
                         let phi =
                           let uu____5275 = FStar_Syntax_Util.arrow_formals t in
                           match uu____5275 with
                           | (uu____5282, t1) ->
                               let uu____5288 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1 in
                               if uu____5288
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond in
                         let uu____5290 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                         (match uu____5290 with
                          | (phi1, uu____5298) ->
                              ((let uu____5300 =
                                  FStar_TypeChecker_Env.should_verify env2 in
                                if uu____5300
                                then
                                  let uu____5301 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1) in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5301
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l ->
                                       fun uu____5318 ->
                                         match uu____5318 with
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
                let uu____5386 =
                  let uu____5387 = FStar_Syntax_Subst.compress t in
                  uu____5387.FStar_Syntax_Syntax.n in
                match uu____5386 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5394) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5431 = is_mutual t' in
                    if uu____5431
                    then true
                    else
                      (let uu____5433 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5433)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5453) ->
                    is_mutual t'
                | uu____5458 -> false
              and exists_mutual uu___1_5459 =
                match uu___1_5459 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5478 =
                let uu____5479 = FStar_Syntax_Subst.compress dt1 in
                uu____5479.FStar_Syntax_Syntax.n in
              match uu____5478 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5485) ->
                  let dbs1 =
                    let uu____5515 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5515 in
                  let dbs2 =
                    let uu____5565 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5565 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5583 =
                               let uu____5584 =
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                               [uu____5584] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.t_haseq uu____5583
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5614 = is_mutual sort in
                             if uu____5614
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5624 =
                             let uu____5625 =
                               let uu____5634 =
                                 let uu____5635 =
                                   FStar_Syntax_Subst.close [b] t in
                                 FStar_Syntax_Util.abs
                                   [((FStar_Pervasives_Native.fst b),
                                      FStar_Pervasives_Native.None)]
                                   uu____5635 FStar_Pervasives_Native.None in
                               FStar_Syntax_Syntax.as_arg uu____5634 in
                             [uu____5625] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.tforall uu____5624
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5682 -> acc
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
              let uu____5731 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____5753, bs, t, uu____5756, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5768 -> failwith "Impossible!" in
              match uu____5731 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____5791 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____5791 t in
                  let uu____5800 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____5800 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____5810 =
                           let uu____5811 = FStar_Syntax_Subst.compress t2 in
                           uu____5811.FStar_Syntax_Syntax.n in
                         match uu____5810 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5815) ->
                             ibs
                         | uu____5836 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____5845 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____5846 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5845
                           uu____5846 in
                       let ind1 =
                         let uu____5850 =
                           FStar_List.map
                             (fun uu____5867 ->
                                match uu____5867 with
                                | (bv, aq) ->
                                    let uu____5886 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5886, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____5850
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____5890 =
                           FStar_List.map
                             (fun uu____5907 ->
                                match uu____5907 with
                                | (bv, aq) ->
                                    let uu____5926 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____5926, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5890
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____5930 =
                           let uu____5931 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____5931] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____5930
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5967, uu____5968, uu____5969, t_lid,
                                   uu____5971, uu____5972)
                                  -> t_lid = lid
                              | uu____5977 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___914_5987 = fml in
                         let uu____5988 =
                           let uu____5989 =
                             let uu____5996 =
                               let uu____5997 =
                                 let uu____6018 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1 in
                                 let uu____6023 =
                                   let uu____6036 =
                                     let uu____6047 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind in
                                     [uu____6047] in
                                   [uu____6036] in
                                 (uu____6018, uu____6023) in
                               FStar_Syntax_Syntax.Meta_pattern uu____5997 in
                             (fml, uu____5996) in
                           FStar_Syntax_Syntax.Tm_meta uu____5989 in
                         {
                           FStar_Syntax_Syntax.n = uu____5988;
                           FStar_Syntax_Syntax.pos =
                             (uu___914_5987.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___914_5987.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6116 =
                                  let uu____6117 =
                                    let uu____6126 =
                                      let uu____6127 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6127
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6126 in
                                  [uu____6117] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6116
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6180 =
                                  let uu____6181 =
                                    let uu____6190 =
                                      let uu____6191 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____6191
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____6190 in
                                  [uu____6181] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____6180
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
                     (lid, uu____6282, uu____6283, uu____6284, uu____6285,
                      uu____6286)
                     -> lid
                 | uu____6295 -> failwith "Impossible!") tcs in
          let uu____6296 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6308, uu____6309, uu____6310, uu____6311) ->
                (lid, us)
            | uu____6320 -> failwith "Impossible!" in
          match uu____6296 with
          | (lid, us) ->
              let uu____6329 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6329 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6356 =
                       let uu____6357 =
                         let uu____6364 = get_haseq_axiom_lid lid in
                         (uu____6364, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6357 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6356;
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
          let uu____6417 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6443 ->
                    match uu___2_6443 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6444;
                        FStar_Syntax_Syntax.sigrng = uu____6445;
                        FStar_Syntax_Syntax.sigquals = uu____6446;
                        FStar_Syntax_Syntax.sigmeta = uu____6447;
                        FStar_Syntax_Syntax.sigattrs = uu____6448;
                        FStar_Syntax_Syntax.sigopts = uu____6449;_} -> true
                    | uu____6472 -> false)) in
          match uu____6417 with
          | (tys, datas) ->
              ((let uu____6494 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6504 ->
                          match uu___3_6504 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6505;
                              FStar_Syntax_Syntax.sigrng = uu____6506;
                              FStar_Syntax_Syntax.sigquals = uu____6507;
                              FStar_Syntax_Syntax.sigmeta = uu____6508;
                              FStar_Syntax_Syntax.sigattrs = uu____6509;
                              FStar_Syntax_Syntax.sigopts = uu____6510;_} ->
                              false
                          | uu____6531 -> true)) in
                if uu____6494
                then
                  let uu____6532 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6532
                else ());
               (let univs =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6540 =
                       let uu____6541 = FStar_List.hd tys in
                       uu____6541.FStar_Syntax_Syntax.sigel in
                     match uu____6540 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6544, uvs, uu____6546, uu____6547,
                          uu____6548, uu____6549)
                         -> uvs
                     | uu____6558 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6562 =
                  FStar_List.fold_right
                    (fun tc ->
                       fun uu____6601 ->
                         match uu____6601 with
                         | (env1, all_tcs, g) ->
                             let uu____6641 = tc_tycon env1 tc in
                             (match uu____6641 with
                              | (env2, tc1, tc_u, guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____6668 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____6668
                                    then
                                      let uu____6669 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____6669
                                    else ());
                                   (let uu____6671 =
                                      let uu____6672 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____6672 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____6671))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard) in
                match uu____6562 with
                | (env1, tcs, g) ->
                    let uu____6718 =
                      FStar_List.fold_right
                        (fun se ->
                           fun uu____6740 ->
                             match uu____6740 with
                             | (datas1, g1) ->
                                 let uu____6759 =
                                   let uu____6764 = tc_data env1 tcs in
                                   uu____6764 se in
                                 (match uu____6759 with
                                  | (data, g') ->
                                      let uu____6781 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____6781))) datas
                        ([], g) in
                    (match uu____6718 with
                     | (datas1, g1) ->
                         let uu____6802 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs in
                           let g2 =
                             let uu___1025_6819 = g1 in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1025_6819.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred_to_tac =
                                 (uu___1025_6819.FStar_TypeChecker_Common.deferred_to_tac);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1025_6819.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1025_6819.FStar_TypeChecker_Common.implicits)
                             } in
                           (let uu____6829 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses") in
                            if uu____6829
                            then
                              let uu____6830 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____6830
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____6842 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs in
                              (uu____6842, datas1)) in
                         (match uu____6802 with
                          | (tcs1, datas2) ->
                              let sig_bndle =
                                let uu____6874 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____6875 =
                                  FStar_List.collect
                                    (fun s -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____6874;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____6875;
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
                                            uu____6901, uu____6902)
                                           ->
                                           let fail expected inferred =
                                             let uu____6922 =
                                               let uu____6927 =
                                                 let uu____6928 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu____6929 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____6928 uu____6929 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____6927) in
                                             FStar_Errors.raise_error
                                               uu____6922
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu____6930 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____6930 with
                                            | FStar_Pervasives_Native.None ->
                                                ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ, uu____6946) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____6977 ->
                                                        let uu____6978 =
                                                          let uu____6979 =
                                                            let uu____6994 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                typ in
                                                            (binders,
                                                              uu____6994) in
                                                          FStar_Syntax_Syntax.Tm_arrow
                                                            uu____6979 in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____6978
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs1, body) in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ))
                                                then
                                                  let uu____7015 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____7015 with
                                                   | (uu____7020, inferred)
                                                       ->
                                                       let uu____7022 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ in
                                                       (match uu____7022 with
                                                        | (uu____7027,
                                                           expected) ->
                                                            let uu____7029 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected in
                                                            if uu____7029
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ
                                                                inferred_typ))
                                                else
                                                  fail expected_typ
                                                    inferred_typ)
                                       | uu____7032 -> ()));
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
                              let uu____7136 =
                                let uu____7137 =
                                  let uu____7144 =
                                    let uu____7147 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7147 in
                                  (uu____7144, inst_univs) in
                                FStar_Syntax_Syntax.Tm_uinst uu____7137 in
                              FStar_Syntax_Syntax.mk uu____7136 p in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7181 ->
                                      match uu____7181 with
                                      | (x, imp) ->
                                          let uu____7200 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____7200, imp))) in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args p in
                          let unrefined_arg_binder =
                            let uu____7204 = projectee arg_typ in
                            FStar_Syntax_Syntax.mk_binder uu____7204 in
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
                                   let uu____7225 =
                                     FStar_Ident.set_lid_range disc_name p in
                                   FStar_Syntax_Syntax.fvar uu____7225
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None in
                                 let uu____7226 =
                                   let uu____7229 =
                                     let uu____7232 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs in
                                     let uu____7233 =
                                       let uu____7234 =
                                         let uu____7243 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7243 in
                                       [uu____7234] in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7232
                                       uu____7233 p in
                                   FStar_Syntax_Util.b2t uu____7229 in
                                 FStar_Syntax_Util.refine x uu____7226 in
                               let uu____7268 =
                                 let uu___1100_7269 = projectee arg_typ in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1100_7269.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1100_7269.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 } in
                               FStar_Syntax_Syntax.mk_binder uu____7268) in
                          let ntps = FStar_List.length tps in
                          let all_params =
                            let uu____7286 =
                              FStar_List.map
                                (fun uu____7310 ->
                                   match uu____7310 with
                                   | (x, uu____7324) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps in
                            FStar_List.append uu____7286 fields in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7383 ->
                                    match uu____7383 with
                                    | (x, uu____7397) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)))) in
                          let early_prims_inductive =
                            (let uu____7407 =
                               FStar_TypeChecker_Env.current_module env in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7407)
                              &&
                              (FStar_List.existsb
                                 (fun s ->
                                    let uu____7411 =
                                      let uu____7412 =
                                        FStar_Ident.ident_of_lid tc in
                                      FStar_Ident.string_of_id uu____7412 in
                                    s = uu____7411) early_prims_inductives) in
                          let discriminator_ses =
                            if fvq <> FStar_Syntax_Syntax.Data_ctor
                            then []
                            else
                              (let discriminator_name =
                                 FStar_Syntax_Util.mk_discriminator lid in
                               let no_decl = false in
                               let only_decl =
                                 early_prims_inductive ||
                                   (let uu____7423 =
                                      let uu____7424 =
                                        FStar_TypeChecker_Env.current_module
                                          env in
                                      FStar_Ident.string_of_lid uu____7424 in
                                    FStar_Options.dont_gen_projectors
                                      uu____7423) in
                               let quals =
                                 let uu____7428 =
                                   FStar_List.filter
                                     (fun uu___4_7432 ->
                                        match uu___4_7432 with
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                            -> true
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu____7433 -> false) iquals in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____7428 in
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
                                 let uu____7473 =
                                   FStar_Syntax_Util.arrow binders bool_typ in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____7473 in
                               let decl =
                                 let uu____7477 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____7477;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               (let uu____7479 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes") in
                                if uu____7479
                                then
                                  let uu____7480 =
                                    FStar_Syntax_Print.sigelt_to_string decl in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____7480
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
                                                 fun uu____7531 ->
                                                   match uu____7531 with
                                                   | (x, imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____7551 =
                                                           let uu____7554 =
                                                             let uu____7555 =
                                                               let uu____7562
                                                                 =
                                                                 let uu____7563
                                                                   =
                                                                   FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   uu____7563
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun in
                                                               (uu____7562,
                                                                 FStar_Syntax_Syntax.tun) in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____7555 in
                                                           pos uu____7554 in
                                                         (uu____7551, b)
                                                       else
                                                         (let uu____7569 =
                                                            let uu____7572 =
                                                              let uu____7573
                                                                =
                                                                let uu____7574
                                                                  =
                                                                  FStar_Ident.string_of_id
                                                                    x.FStar_Syntax_Syntax.ppname in
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  uu____7574
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____7573 in
                                                            pos uu____7572 in
                                                          (uu____7569, b)))) in
                                       let pat_true =
                                         let uu____7592 =
                                           let uu____7595 =
                                             let uu____7596 =
                                               let uu____7609 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq) in
                                               (uu____7609, arg_pats) in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____7596 in
                                           pos uu____7595 in
                                         (uu____7592,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool) in
                                       let pat_false =
                                         let uu____7643 =
                                           let uu____7646 =
                                             let uu____7647 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____7647 in
                                           pos uu____7646 in
                                         (uu____7643,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool) in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder) in
                                       let uu____7661 =
                                         let uu____7662 =
                                           let uu____7685 =
                                             let uu____7702 =
                                               FStar_Syntax_Util.branch
                                                 pat_true in
                                             let uu____7717 =
                                               let uu____7734 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false in
                                               [uu____7734] in
                                             uu____7702 :: uu____7717 in
                                           (arg_exp, uu____7685) in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____7662 in
                                       FStar_Syntax_Syntax.mk uu____7661 p) in
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
                                    let uu____7820 =
                                      let uu____7825 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None in
                                      FStar_Util.Inr uu____7825 in
                                    let uu____7826 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____7820 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____7826 [] FStar_Range.dummyRange in
                                  let impl =
                                    let uu____7832 =
                                      let uu____7833 =
                                        let uu____7840 =
                                          let uu____7843 =
                                            let uu____7844 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right in
                                            FStar_All.pipe_right uu____7844
                                              (fun fv ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                          [uu____7843] in
                                        ((false, [lb]), uu____7840) in
                                      FStar_Syntax_Syntax.Sig_let uu____7833 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____7832;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    } in
                                  (let uu____7856 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes") in
                                   if uu____7856
                                   then
                                     let uu____7857 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____7857
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
                                    fun uu____7925 ->
                                      match uu____7925 with
                                      | (a, uu____7933) ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i in
                                          let field_proj_tm =
                                            let uu____7940 =
                                              let uu____7941 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____7941 in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu____7940 inst_univs in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg] p in
                                          FStar_Syntax_Syntax.NT (a, proj))) in
                          let projectors_ses =
                            let uu____7964 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu____8004 ->
                                        match uu____8004 with
                                        | (x, uu____8014) ->
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
                                              let uu____8031 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu____8031 in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu____8036 =
                                                   let uu____8037 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env in
                                                   FStar_Ident.string_of_lid
                                                     uu____8037 in
                                                 FStar_Options.dont_gen_projectors
                                                   uu____8036) in
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
                                                     (fun uu___5_8065 ->
                                                        match uu___5_8065
                                                        with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                            -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                            -> true
                                                        | FStar_Syntax_Syntax.Private
                                                            -> true
                                                        | uu____8066 -> false)) in
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
                                              let uu____8074 =
                                                FStar_Ident.range_of_lid
                                                  field_name in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu____8074;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              } in
                                            ((let uu____8076 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes") in
                                              if uu____8076
                                              then
                                                let uu____8077 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu____8077
                                              else ());
                                             if only_decl
                                             then [decl]
                                             else
                                               (let projection =
                                                  let uu____8083 =
                                                    FStar_Ident.string_of_id
                                                      x.FStar_Syntax_Syntax.ppname in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    uu____8083
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Syntax.tun in
                                                let arg_pats =
                                                  FStar_All.pipe_right
                                                    all_params
                                                    (FStar_List.mapi
                                                       (fun j ->
                                                          fun uu____8124 ->
                                                            match uu____8124
                                                            with
                                                            | (x1, imp) ->
                                                                let b =
                                                                  FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                if
                                                                  (i + ntps)
                                                                    = j
                                                                then
                                                                  let uu____8144
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                  (uu____8144,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____8156
                                                                    =
                                                                    let uu____8159
                                                                    =
                                                                    let uu____8160
                                                                    =
                                                                    let uu____8167
                                                                    =
                                                                    let uu____8168
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8168
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8167,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8160 in
                                                                    pos
                                                                    uu____8159 in
                                                                    (uu____8156,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____8174
                                                                    =
                                                                    let uu____8177
                                                                    =
                                                                    let uu____8178
                                                                    =
                                                                    let uu____8179
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    x1.FStar_Syntax_Syntax.ppname in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    uu____8179
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8178 in
                                                                    pos
                                                                    uu____8177 in
                                                                    (uu____8174,
                                                                    b)))) in
                                                let pat =
                                                  let uu____8197 =
                                                    let uu____8200 =
                                                      let uu____8201 =
                                                        let uu____8214 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq) in
                                                        (uu____8214,
                                                          arg_pats) in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____8201 in
                                                    pos uu____8200 in
                                                  let uu____8223 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection in
                                                  (uu____8197,
                                                    FStar_Pervasives_Native.None,
                                                    uu____8223) in
                                                let body =
                                                  let uu____8239 =
                                                    let uu____8240 =
                                                      let uu____8263 =
                                                        let uu____8280 =
                                                          FStar_Syntax_Util.branch
                                                            pat in
                                                        [uu____8280] in
                                                      (arg_exp, uu____8263) in
                                                    FStar_Syntax_Syntax.Tm_match
                                                      uu____8240 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____8239 p1 in
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
                                                  let uu____8352 =
                                                    let uu____8357 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None in
                                                    FStar_Util.Inr uu____8357 in
                                                  let uu____8358 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____8352;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____8358;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  } in
                                                let impl =
                                                  let uu____8364 =
                                                    let uu____8365 =
                                                      let uu____8372 =
                                                        let uu____8375 =
                                                          let uu____8376 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right in
                                                          FStar_All.pipe_right
                                                            uu____8376
                                                            (fun fv ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [uu____8375] in
                                                      ((false, [lb]),
                                                        uu____8372) in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____8365 in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____8364;
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
                                                (let uu____8388 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes") in
                                                 if uu____8388
                                                 then
                                                   let uu____8389 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu____8389
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl])))) in
                            FStar_All.pipe_right uu____7964
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
                (constr_lid, uvs, t, typ_lid, n_typars, uu____8446) when
                let uu____8451 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid in
                Prims.op_Negation uu____8451 ->
                let uu____8452 = FStar_Syntax_Subst.univ_var_opening uvs in
                (match uu____8452 with
                 | (univ_opening, uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t in
                     let uu____8474 = FStar_Syntax_Util.arrow_formals t1 in
                     (match uu____8474 with
                      | (formals, uu____8484) ->
                          let uu____8489 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1 ->
                                   let uu____8521 =
                                     let uu____8522 =
                                       let uu____8523 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____8523 in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____8522 in
                                   if uu____8521
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____8542, uvs', tps, typ0,
                                          uu____8546, constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____8563 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None) in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                let uu____8604 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid in
                                if uu____8604
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng in
                          (match uu____8489 with
                           | (inductive_tps, typ0, should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0 in
                               let uu____8631 =
                                 FStar_Syntax_Util.arrow_formals typ01 in
                               (match uu____8631 with
                                | (indices, uu____8641) ->
                                    let refine_domain =
                                      let uu____8647 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___6_8652 ->
                                                match uu___6_8652 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____8653 -> true
                                                | uu____8662 -> false)) in
                                      if uu____8647
                                      then false
                                      else should_refine in
                                    let fv_qual =
                                      let filter_records uu___7_8672 =
                                        match uu___7_8672 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____8675, fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu____8687 ->
                                            FStar_Pervasives_Native.None in
                                      let uu____8688 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records in
                                      match uu____8688 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q in
                                    let fields =
                                      let uu____8693 =
                                        FStar_Util.first_N n_typars formals in
                                      match uu____8693 with
                                      | (imp_tps, fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____8776 ->
                                                 fun uu____8777 ->
                                                   match (uu____8776,
                                                           uu____8777)
                                                   with
                                                   | ((x, uu____8803),
                                                      (x', uu____8805)) ->
                                                       let uu____8826 =
                                                         let uu____8833 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x' in
                                                         (x, uu____8833) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____8826) imp_tps
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
            | uu____8839 -> []