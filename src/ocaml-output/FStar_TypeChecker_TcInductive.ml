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
      (FStar_TypeChecker_Env.env_t, FStar_Syntax_Syntax.sigelt,
        FStar_Syntax_Syntax.universe, FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple4)
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
                                        ((let uu____289 =
                                            let uu____290 =
                                              FStar_TypeChecker_Rel.subtype_nosmt_force
                                                env1 t t_type in
                                            Prims.op_Negation uu____290 in
                                          if uu____289
                                          then
                                            let uu____291 =
                                              let uu____296 =
                                                let uu____297 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t in
                                                let uu____298 =
                                                  FStar_Ident.string_of_lid
                                                    tc in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not a subtype of Type"
                                                  uu____297 uu____298 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____296) in
                                            FStar_Errors.raise_error
                                              uu____291
                                              s.FStar_Syntax_Syntax.sigrng
                                          else ());
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1 in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 tps3 guard in
                                          let t_tc =
                                            let uu____307 =
                                              let uu____316 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1) in
                                              let uu____333 =
                                                let uu____342 =
                                                  let uu____355 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1 in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____355 in
                                                FStar_All.pipe_right indices
                                                  uu____342 in
                                              FStar_List.append uu____316
                                                uu____333 in
                                            let uu____378 =
                                              let uu____381 =
                                                let uu____382 =
                                                  let uu____387 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1 in
                                                  FStar_Syntax_Subst.subst
                                                    uu____387 in
                                                FStar_All.pipe_right t
                                                  uu____382 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____381 in
                                            FStar_Syntax_Util.arrow uu____307
                                              uu____378 in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3 in
                                          let uu____404 =
                                            let uu____409 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4 in
                                            let uu____410 =
                                              let uu____411 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1 in
                                              FStar_Syntax_Subst.subst
                                                uu____411 k4 in
                                            (uu____409, uu____410) in
                                          match uu____404 with
                                          | (tps5, k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None in
                                              let uu____431 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc) in
                                              (uu____431,
                                                (let uu___356_437 = s in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___356_437.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___356_437.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___356_437.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___356_437.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____442 -> failwith "impossible"
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt, FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt, FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun tcs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (c, _uvs, t, tc_lid, ntps, _mutual_tcs) ->
            let uu____502 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu____502 with
             | (usubst, _uvs1) ->
                 let uu____525 =
                   let uu____530 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu____531 = FStar_Syntax_Subst.subst usubst t in
                   (uu____530, uu____531) in
                 (match uu____525 with
                  | (env1, t1) ->
                      let uu____538 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____577 ->
                               match uu____577 with
                               | (se1, u_tc) ->
                                   let uu____592 =
                                     let uu____593 =
                                       let uu____594 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____594 in
                                     FStar_Ident.lid_equals tc_lid uu____593 in
                                   if uu____592
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____613, uu____614, tps,
                                           uu____616, uu____617, uu____618)
                                          ->
                                          let tps1 =
                                            let uu____628 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu____628
                                              (FStar_List.map
                                                 (fun uu____668 ->
                                                    match uu____668 with
                                                    | (x, uu____682) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag)))) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu____690 =
                                            let uu____697 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu____697, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu____690
                                      | uu____704 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu____745 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu____745
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu____538 with
                       | (env2, tps, u_tc) ->
                           let uu____772 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1 in
                             let uu____788 =
                               let uu____789 = FStar_Syntax_Subst.compress t2 in
                               uu____789.FStar_Syntax_Syntax.n in
                             match uu____788 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu____828 = FStar_Util.first_N ntps bs in
                                 (match uu____828 with
                                  | (uu____869, bs') ->
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
                                                fun uu____940 ->
                                                  match uu____940 with
                                                  | (x, uu____948) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x))) in
                                      let uu____953 =
                                        FStar_Syntax_Subst.subst subst1 t3 in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____953)
                             | uu____954 -> ([], t2) in
                           (match uu____772 with
                            | (arguments, result) ->
                                ((let uu____998 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu____998
                                  then
                                    let uu____999 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu____1000 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu____1001 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____999 uu____1000 uu____1001
                                  else ());
                                 (let uu____1003 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu____1003 with
                                  | (arguments1, env', us) ->
                                      let uu____1017 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result in
                                      (match uu____1017 with
                                       | (result1, res_lcomp) ->
                                           let ty =
                                             let uu____1029 =
                                               unfold_whnf env2
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_All.pipe_right uu____1029
                                               FStar_Syntax_Util.unrefine in
                                           ((let uu____1031 =
                                               let uu____1032 =
                                                 FStar_Syntax_Subst.compress
                                                   ty in
                                               uu____1032.FStar_Syntax_Syntax.n in
                                             match uu____1031 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____1035 -> ()
                                             | uu____1036 ->
                                                 let uu____1037 =
                                                   let uu____1042 =
                                                     let uu____1043 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1 in
                                                     let uu____1044 =
                                                       FStar_Syntax_Print.term_to_string
                                                         ty in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____1043 uu____1044 in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____1042) in
                                                 FStar_Errors.raise_error
                                                   uu____1037
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____1045 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1 in
                                             match uu____1045 with
                                             | (head1, uu____1067) ->
                                                 let g_uvs =
                                                   let uu____1093 =
                                                     let uu____1094 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____1094.FStar_Syntax_Syntax.n in
                                                   match uu____1093 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____1098;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____1099;_},
                                                        tuvs)
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
                                                                  let uu____1112
                                                                    =
                                                                    let uu____1113
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    let uu____1114
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'
                                                                    uu____1113
                                                                    uu____1114 in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1112)
                                                           FStar_TypeChecker_Env.trivial_guard
                                                           tuvs _uvs1
                                                       else
                                                         failwith
                                                           "Impossible: tc_datacon: length of annotated universes not same as instantiated ones"
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv tc_lid
                                                       ->
                                                       FStar_TypeChecker_Env.trivial_guard
                                                   | uu____1117 ->
                                                       let uu____1118 =
                                                         let uu____1123 =
                                                           let uu____1124 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid in
                                                           let uu____1125 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1 in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____1124
                                                             uu____1125 in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____1123) in
                                                       FStar_Errors.raise_error
                                                         uu____1118
                                                         se.FStar_Syntax_Syntax.sigrng in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g ->
                                                        fun uu____1140 ->
                                                          fun u_x ->
                                                            match uu____1140
                                                            with
                                                            | (x, uu____1149)
                                                                ->
                                                                let uu____1154
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____1154)
                                                     g_uvs arguments1 us in
                                                 let t2 =
                                                   let uu____1158 =
                                                     let uu____1167 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1207
                                                               ->
                                                               match uu____1207
                                                               with
                                                               | (x,
                                                                  uu____1221)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                     FStar_List.append
                                                       uu____1167 arguments1 in
                                                   let uu____1234 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1 in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1158 uu____1234 in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2 in
                                                 ((let uu___357_1239 = se in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___357_1239.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___357_1239.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___357_1239.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___357_1239.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1242 -> failwith "impossible"
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt, FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun g ->
      fun tcs ->
        fun datas ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs in
          let g1 =
            let uu___358_1307 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___358_1307.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___358_1307.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___358_1307.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____1317 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____1317
           then
             let uu____1318 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1318
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1358 ->
                     match uu____1358 with
                     | (se, uu____1364) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1365, uu____1366, tps, k, uu____1369,
                               uu____1370)
                              ->
                              let uu____1379 =
                                let uu____1380 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1380 in
                              FStar_Syntax_Syntax.null_binder uu____1379
                          | uu____1385 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1413, uu____1414, t, uu____1416, uu____1417,
                          uu____1418)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1423 -> failwith "Impossible")) in
           let t =
             let uu____1427 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1427 in
           (let uu____1437 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1437
            then
              let uu____1438 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1438
            else ());
           (let uu____1440 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1440 with
            | (uvs, t1) ->
                ((let uu____1460 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1460
                  then
                    let uu____1461 =
                      let uu____1462 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1462
                        (FStar_String.concat ", ") in
                    let uu____1473 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1461 uu____1473
                  else ());
                 (let uu____1475 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1475 with
                  | (uvs1, t2) ->
                      let uu____1490 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1490 with
                       | (args, uu____1514) ->
                           let uu____1535 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1535 with
                            | (tc_types, data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1640 ->
                                       fun uu____1641 ->
                                         match (uu____1640, uu____1641) with
                                         | ((x, uu____1663),
                                            (se, uu____1665)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc, uu____1681, tps,
                                                   uu____1683, mutuals,
                                                   datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1695 =
                                                    let uu____1700 =
                                                      let uu____1701 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1701.FStar_Syntax_Syntax.n in
                                                    match uu____1700 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1, c) ->
                                                        let uu____1730 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1730
                                                         with
                                                         | (tps1, rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1808
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1827 -> ([], ty) in
                                                  (match uu____1695 with
                                                   | (tps1, t3) ->
                                                       let uu___359_1836 = se in
                                                       {
                                                         FStar_Syntax_Syntax.sigel
                                                           =
                                                           (FStar_Syntax_Syntax.Sig_inductive_typ
                                                              (tc, uvs1,
                                                                tps1, t3,
                                                                mutuals,
                                                                datas1));
                                                         FStar_Syntax_Syntax.sigrng
                                                           =
                                                           (uu___359_1836.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___359_1836.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___359_1836.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___359_1836.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1841 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1847 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_16 ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_16)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___347_1869 ->
                                                match uu___347_1869 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc, uu____1875,
                                                       uu____1876,
                                                       uu____1877,
                                                       uu____1878,
                                                       uu____1879);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1880;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1881;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1882;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1883;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1896 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1919 ->
                                           fun d ->
                                             match uu____1919 with
                                             | (t3, uu____1928) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l, uu____1934,
                                                       uu____1935, tc, ntps,
                                                       mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1944 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1944
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___360_1945 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___360_1945.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___360_1945.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___360_1945.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___360_1945.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1948 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env ->
    fun s ->
      let uu____1963 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1963
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____1975 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1975
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv, FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____1991 =
      let uu____1992 = FStar_Syntax_Subst.compress t in
      uu____1992.FStar_Syntax_Syntax.n in
    match uu____1991 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2011 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2016 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident, FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list
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
          let uu____2069 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2138 ->
               match uu____2138 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2181 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2181 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2069
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          (let uu____2425 =
             let uu____2426 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____2426 in
           debug_log env uu____2425);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype in
           (let uu____2429 =
              let uu____2430 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2430 in
            debug_log env uu____2429);
           (let uu____2433 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2433) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2444 =
                  let uu____2445 = FStar_Syntax_Subst.compress btype1 in
                  uu____2445.FStar_Syntax_Syntax.n in
                match uu____2444 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let uu____2474 = try_get_fv t in
                    (match uu____2474 with
                     | (fv, us) ->
                         let uu____2481 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid in
                         if uu____2481
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2493 ->
                                 match uu____2493 with
                                 | (t1, uu____2501) ->
                                     let uu____2506 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2506) args)
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
                          let uu____2556 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                          FStar_All.pipe_right uu____2556
                            FStar_Syntax_Syntax.mk_Comp in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2560 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1) in
                           FStar_All.pipe_right uu____2560
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
                            (fun uu____2580 ->
                               match uu____2580 with
                               | (b, uu____2588) ->
                                   let uu____2593 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2593) sbs)
                           &&
                           ((let uu____2598 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2598 with
                             | (uu____2603, return_type) ->
                                 let uu____2605 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2605)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2626 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2628 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2631) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2658) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2684, branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2742 ->
                          match uu____2742 with
                          | (p, uu____2754, t) ->
                              let bs =
                                let uu____2773 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2773 in
                              let uu____2782 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2782 with
                               | (bs1, t1) ->
                                   let uu____2789 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2789)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2811, uu____2812)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2874 ->
                    ((let uu____2876 =
                        let uu____2877 =
                          let uu____2878 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2879 =
                            let uu____2880 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2880 in
                          Prims.strcat uu____2878 uu____2879 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2877 in
                      debug_log env uu____2876);
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
              (let uu____2898 =
                 let uu____2899 =
                   let uu____2900 =
                     let uu____2901 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2901 in
                   Prims.strcat ilid.FStar_Ident.str uu____2900 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2899 in
               debug_log env uu____2898);
              (let uu____2902 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2902 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2915 =
                       FStar_TypeChecker_Env.lookup_attrs_of_lid env ilid in
                     (match uu____2915 with
                      | FStar_Pervasives_Native.None ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some [] ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some attrs ->
                          let uu____2931 =
                            FStar_All.pipe_right attrs
                              (FStar_Util.for_some
                                 (fun tm ->
                                    let uu____2938 =
                                      let uu____2939 =
                                        FStar_Syntax_Subst.compress tm in
                                      uu____2939.FStar_Syntax_Syntax.n in
                                    match uu____2938 with
                                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.assume_strictly_positive_attr_lid
                                    | uu____2943 -> false)) in
                          if uu____2931
                          then
                            ((let uu____2945 =
                                let uu____2946 =
                                  FStar_Ident.string_of_lid ilid in
                                FStar_Util.format1
                                  "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                  uu____2946 in
                              debug_log env uu____2945);
                             true)
                          else
                            (debug_log env
                               "Checking nested positivity, not an inductive, return false";
                             false))
                   else
                     (let uu____2950 =
                        already_unfolded ilid args unfolded env in
                      if uu____2950
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____2974 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid in
                           FStar_Option.get uu____2974 in
                         (let uu____2978 =
                            let uu____2979 =
                              let uu____2980 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2980
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2979 in
                          debug_log env uu____2978);
                         (let uu____2982 =
                            let uu____2983 = FStar_ST.op_Bang unfolded in
                            let uu____3029 =
                              let uu____3036 =
                                let uu____3041 =
                                  let uu____3042 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3042 in
                                (ilid, uu____3041) in
                              [uu____3036] in
                            FStar_List.append uu____2983 uu____3029 in
                          FStar_ST.op_Colon_Equals unfolded uu____2982);
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
                    (Prims.strcat
                       "Checking nested positivity in data constructor "
                       (Prims.strcat dlid.FStar_Ident.str
                          (Prims.strcat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____3187 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3187 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3209 ->
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
                         (let uu____3212 =
                            let uu____3213 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3213 in
                          debug_log env uu____3212);
                         (let uu____3214 =
                            let uu____3215 = FStar_Syntax_Subst.compress dt1 in
                            uu____3215.FStar_Syntax_Syntax.n in
                          match uu____3214 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3241 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____3241 with
                                | (ibs, dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____3304 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3304 dbs1 in
                                    let c1 =
                                      let uu____3308 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3308 c in
                                    let uu____3311 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____3311 with
                                     | (args1, uu____3345) ->
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
                                           let uu____3437 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3437 c1 in
                                         ((let uu____3447 =
                                             let uu____3448 =
                                               let uu____3449 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____3450 =
                                                 let uu____3451 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____3451 in
                                               Prims.strcat uu____3449
                                                 uu____3450 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3448 in
                                           debug_log env uu____3447);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3482 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3484 =
                                  let uu____3485 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____3485.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____3484
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
                   (let uu____3551 = try_get_fv t1 in
                    match uu____3551 with
                    | (fv, uu____3557) ->
                        let uu____3558 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____3558
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  ((let uu____3583 =
                      let uu____3584 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3584 in
                    debug_log env uu____3583);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3586 =
                      FStar_List.fold_left
                        (fun uu____3605 ->
                           fun b ->
                             match uu____3605 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3628 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3651 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3628, uu____3651))) (true, env)
                        sbs1 in
                    match uu____3586 with | (b, uu____3665) -> b))
              | uu____3666 ->
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
              let uu____3717 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3717 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3739 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3741 =
                      let uu____3742 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____3742 in
                    debug_log env uu____3741);
                   (let uu____3743 =
                      let uu____3744 = FStar_Syntax_Subst.compress dt in
                      uu____3744.FStar_Syntax_Syntax.n in
                    match uu____3743 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3747 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3750) ->
                        let dbs1 =
                          let uu____3780 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3780 in
                        let dbs2 =
                          let uu____3830 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3830 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3835 =
                            let uu____3836 =
                              let uu____3837 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____3837 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3836 in
                          debug_log env uu____3835);
                         (let uu____3844 =
                            FStar_List.fold_left
                              (fun uu____3863 ->
                                 fun b ->
                                   match uu____3863 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3886 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3909 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3886, uu____3909)))
                              (true, env) dbs3 in
                          match uu____3844 with | (b, uu____3923) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3924, uu____3925) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3978 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3996 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____4012, uu____4013, uu____4014) ->
            (lid, us, bs)
        | uu____4023 -> failwith "Impossible!" in
      match uu____3996 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____4033 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____4033 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____4056 =
                 let uu____4059 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____4059 in
               FStar_List.for_all
                 (fun d ->
                    let uu____4071 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4071
                      unfolded_inductives env2) uu____4056)
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4101, uu____4102, t, uu____4104, uu____4105, uu____4106) -> t
    | uu____4111 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = lid.FStar_Ident.str in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____4131 =
         let uu____4132 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____4132 haseq_suffix in
       uu____4131 = (Prims.parse_int "0"))
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____4152 =
      let uu____4155 =
        let uu____4158 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix) in
        [uu____4158] in
      FStar_List.append lid.FStar_Ident.ns uu____4155 in
    FStar_Ident.lid_of_ids uu____4152
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident, FStar_Syntax_Syntax.term,
            FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple5)
  =
  fun en ->
    fun ty ->
      fun usubst ->
        fun us ->
          let uu____4203 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4217, bs, t, uu____4220, uu____4221) ->
                (lid, bs, t)
            | uu____4230 -> failwith "Impossible!" in
          match uu____4203 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____4252 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____4252 t in
              let uu____4261 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____4261 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____4279 =
                       let uu____4280 = FStar_Syntax_Subst.compress t2 in
                       uu____4280.FStar_Syntax_Syntax.n in
                     match uu____4279 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4284) -> ibs
                     | uu____4305 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____4314 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____4315 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4314 uu____4315 in
                   let ind1 =
                     let uu____4321 =
                       let uu____4326 =
                         FStar_List.map
                           (fun uu____4343 ->
                              match uu____4343 with
                              | (bv, aq) ->
                                  let uu____4362 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____4362, aq)) bs2 in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4326 in
                     uu____4321 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____4370 =
                       let uu____4375 =
                         FStar_List.map
                           (fun uu____4392 ->
                              match uu____4392 with
                              | (bv, aq) ->
                                  let uu____4411 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____4411, aq)) ibs1 in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4375 in
                     uu____4370 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____4419 =
                       let uu____4424 =
                         let uu____4425 = FStar_Syntax_Syntax.as_arg ind2 in
                         [uu____4425] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4424 in
                     uu____4419 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____4476 =
                            let uu____4477 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____4477 in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4476) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____4490 =
                              let uu____4493 =
                                let uu____4498 =
                                  let uu____4499 =
                                    let uu____4508 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b) in
                                    FStar_Syntax_Syntax.as_arg uu____4508 in
                                  [uu____4499] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4498 in
                              uu____4493 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____4490)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___361_4533 = fml in
                     let uu____4534 =
                       let uu____4535 =
                         let uu____4542 =
                           let uu____4543 =
                             let uu____4556 =
                               let uu____4567 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind in
                               [uu____4567] in
                             [uu____4556] in
                           FStar_Syntax_Syntax.Meta_pattern uu____4543 in
                         (fml, uu____4542) in
                       FStar_Syntax_Syntax.Tm_meta uu____4535 in
                     {
                       FStar_Syntax_Syntax.n = uu____4534;
                       FStar_Syntax_Syntax.pos =
                         (uu___361_4533.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___361_4533.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4622 =
                              let uu____4627 =
                                let uu____4628 =
                                  let uu____4637 =
                                    let uu____4638 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4638 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____4637 in
                                [uu____4628] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4627 in
                            uu____4622 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____4695 =
                              let uu____4700 =
                                let uu____4701 =
                                  let uu____4710 =
                                    let uu____4711 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4711 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____4710 in
                                [uu____4701] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4700 in
                            uu____4695 FStar_Pervasives_Native.None
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
          let uu____4787 =
            let uu____4788 = FStar_Syntax_Subst.compress dt1 in
            uu____4788.FStar_Syntax_Syntax.n in
          match uu____4787 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4792) ->
              let dbs1 =
                let uu____4822 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4822 in
              let dbs2 =
                let uu____4872 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4872 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4887 =
                           let uu____4892 =
                             let uu____4893 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____4893] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4892 in
                         uu____4887 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4926 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____4926 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4934 =
                       let uu____4939 =
                         let uu____4940 =
                           let uu____4949 =
                             let uu____4950 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4950
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____4949 in
                         [uu____4940] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4939 in
                     uu____4934 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4999 -> FStar_Syntax_Util.t_true
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident, FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,
          FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple4 ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident, FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple2 Prims.list,
              FStar_TypeChecker_Env.env,
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple4)
  =
  fun all_datas_in_the_bundle ->
    fun usubst ->
      fun us ->
        fun acc ->
          fun ty ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid, uu____5089, uu____5090, uu____5091, uu____5092,
                   uu____5093)
                  -> lid
              | uu____5102 -> failwith "Impossible!" in
            let uu____5103 = acc in
            match uu____5103 with
            | (uu____5140, en, uu____5142, uu____5143) ->
                let uu____5164 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____5164 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____5201 = acc in
                     (match uu____5201 with
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
                                     (uu____5275, uu____5276, uu____5277,
                                      t_lid, uu____5279, uu____5280)
                                     -> t_lid = lid
                                 | uu____5285 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5298 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5298)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5301 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5304 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5301, uu____5304)))
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
          let us =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5363, us, uu____5365, uu____5366, uu____5367,
                 uu____5368)
                -> us
            | uu____5377 -> failwith "Impossible!" in
          let uu____5378 = FStar_Syntax_Subst.univ_var_opening us in
          match uu____5378 with
          | (usubst, us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                let uu____5403 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs in
                match uu____5403 with
                | (axioms, env2, guard, cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond in
                    let uu____5481 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                    (match uu____5481 with
                     | (phi1, uu____5489) ->
                         ((let uu____5491 =
                             FStar_TypeChecker_Env.should_verify env2 in
                           if uu____5491
                           then
                             let uu____5492 =
                               FStar_TypeChecker_Env.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1) in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____5492
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l ->
                                  fun uu____5509 ->
                                    match uu____5509 with
                                    | (lid, fml) ->
                                        let fml1 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            us1 fml in
                                        FStar_List.append l
                                          [{
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_assume
                                                  (lid, us1, fml1));
                                             FStar_Syntax_Syntax.sigrng =
                                               FStar_Range.dummyRange;
                                             FStar_Syntax_Syntax.sigquals =
                                               [];
                                             FStar_Syntax_Syntax.sigmeta =
                                               FStar_Syntax_Syntax.default_sigmeta;
                                             FStar_Syntax_Syntax.sigattrs =
                                               []
                                           }]) [] axioms in
                           (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                             "haseq";
                           ses)))))
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
                let uu____5577 =
                  let uu____5578 = FStar_Syntax_Subst.compress t in
                  uu____5578.FStar_Syntax_Syntax.n in
                match uu____5577 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5585) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5622 = is_mutual t' in
                    if uu____5622
                    then true
                    else
                      (let uu____5624 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5624)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5644) ->
                    is_mutual t'
                | uu____5649 -> false
              and exists_mutual uu___348_5650 =
                match uu___348_5650 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5669 =
                let uu____5670 = FStar_Syntax_Subst.compress dt1 in
                uu____5670.FStar_Syntax_Syntax.n in
              match uu____5669 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5676) ->
                  let dbs1 =
                    let uu____5706 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5706 in
                  let dbs2 =
                    let uu____5756 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5756 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5776 =
                               let uu____5781 =
                                 let uu____5782 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____5782] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5781 in
                             uu____5776 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5814 = is_mutual sort in
                             if uu____5814
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5826 =
                             let uu____5831 =
                               let uu____5832 =
                                 let uu____5841 =
                                   let uu____5842 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5842 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____5841 in
                               [uu____5832] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5831 in
                           uu____5826 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5891 -> acc
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
              let uu____5940 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____5962, bs, t, uu____5965, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5977 -> failwith "Impossible!" in
              match uu____5940 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____6000 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____6000 t in
                  let uu____6009 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____6009 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____6019 =
                           let uu____6020 = FStar_Syntax_Subst.compress t2 in
                           uu____6020.FStar_Syntax_Syntax.n in
                         match uu____6019 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____6024) ->
                             ibs
                         | uu____6045 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____6054 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____6055 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6054
                           uu____6055 in
                       let ind1 =
                         let uu____6061 =
                           let uu____6066 =
                             FStar_List.map
                               (fun uu____6083 ->
                                  match uu____6083 with
                                  | (bv, aq) ->
                                      let uu____6102 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6102, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6066 in
                         uu____6061 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____6110 =
                           let uu____6115 =
                             FStar_List.map
                               (fun uu____6132 ->
                                  match uu____6132 with
                                  | (bv, aq) ->
                                      let uu____6151 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6151, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6115 in
                         uu____6110 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____6159 =
                           let uu____6164 =
                             let uu____6165 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____6165] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6164 in
                         uu____6159 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6203, uu____6204, uu____6205, t_lid,
                                   uu____6207, uu____6208)
                                  -> t_lid = lid
                              | uu____6213 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___362_6223 = fml in
                         let uu____6224 =
                           let uu____6225 =
                             let uu____6232 =
                               let uu____6233 =
                                 let uu____6246 =
                                   let uu____6257 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____6257] in
                                 [uu____6246] in
                               FStar_Syntax_Syntax.Meta_pattern uu____6233 in
                             (fml, uu____6232) in
                           FStar_Syntax_Syntax.Tm_meta uu____6225 in
                         {
                           FStar_Syntax_Syntax.n = uu____6224;
                           FStar_Syntax_Syntax.pos =
                             (uu___362_6223.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___362_6223.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6312 =
                                  let uu____6317 =
                                    let uu____6318 =
                                      let uu____6327 =
                                        let uu____6328 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6328
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6327 in
                                    [uu____6318] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6317 in
                                uu____6312 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6385 =
                                  let uu____6390 =
                                    let uu____6391 =
                                      let uu____6400 =
                                        let uu____6401 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6401
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6400 in
                                    [uu____6391] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6390 in
                                uu____6385 FStar_Pervasives_Native.None
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
                     (lid, uu____6494, uu____6495, uu____6496, uu____6497,
                      uu____6498)
                     -> lid
                 | uu____6507 -> failwith "Impossible!") tcs in
          let uu____6508 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6520, uu____6521, uu____6522, uu____6523) ->
                (lid, us)
            | uu____6532 -> failwith "Impossible!" in
          match uu____6508 with
          | (lid, us) ->
              let uu____6541 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6541 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6568 =
                       let uu____6569 =
                         let uu____6576 = get_haseq_axiom_lid lid in
                         (uu____6576, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6569 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6568;
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
          (FStar_Syntax_Syntax.sigelt, FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let uu____6629 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___349_6654 ->
                    match uu___349_6654 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6655;
                        FStar_Syntax_Syntax.sigrng = uu____6656;
                        FStar_Syntax_Syntax.sigquals = uu____6657;
                        FStar_Syntax_Syntax.sigmeta = uu____6658;
                        FStar_Syntax_Syntax.sigattrs = uu____6659;_} -> true
                    | uu____6680 -> false)) in
          match uu____6629 with
          | (tys, datas) ->
              ((let uu____6702 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___350_6711 ->
                          match uu___350_6711 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6712;
                              FStar_Syntax_Syntax.sigrng = uu____6713;
                              FStar_Syntax_Syntax.sigquals = uu____6714;
                              FStar_Syntax_Syntax.sigmeta = uu____6715;
                              FStar_Syntax_Syntax.sigattrs = uu____6716;_} ->
                              false
                          | uu____6735 -> true)) in
                if uu____6702
                then
                  let uu____6736 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6736
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6744 =
                       let uu____6745 = FStar_List.hd tys in
                       uu____6745.FStar_Syntax_Syntax.sigel in
                     match uu____6744 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6748, uvs, uu____6750, uu____6751,
                          uu____6752, uu____6753)
                         -> uvs
                     | uu____6762 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6766 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6792 =
                       FStar_Syntax_Subst.univ_var_opening univs1 in
                     match uu____6792 with
                     | (subst1, univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid, uu____6830, bs, t, l1, l2) ->
                                      let uu____6843 =
                                        let uu____6860 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs in
                                        let uu____6861 =
                                          let uu____6862 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1 in
                                          FStar_Syntax_Subst.subst uu____6862
                                            t in
                                        (lid, univs2, uu____6860, uu____6861,
                                          l1, l2) in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6843
                                  | uu____6875 ->
                                      failwith "Impossible, can't happen" in
                                let uu___363_6876 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___363_6876.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___363_6876.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___363_6876.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___363_6876.FStar_Syntax_Syntax.sigattrs)
                                }) tys in
                         let datas1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid, uu____6886, t, lid_t, x, l) ->
                                      let uu____6895 =
                                        let uu____6910 =
                                          FStar_Syntax_Subst.subst subst1 t in
                                        (lid, univs2, uu____6910, lid_t, x,
                                          l) in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6895
                                  | uu____6913 ->
                                      failwith "Impossible, can't happen" in
                                let uu___364_6914 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___364_6914.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___364_6914.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___364_6914.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___364_6914.FStar_Syntax_Syntax.sigattrs)
                                }) datas in
                         let uu____6915 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2 in
                         (uu____6915, tys1, datas1)) in
                match uu____6766 with
                | (env1, tys1, datas1) ->
                    let uu____6941 =
                      FStar_List.fold_right
                        (fun tc ->
                           fun uu____6980 ->
                             match uu____6980 with
                             | (env2, all_tcs, g) ->
                                 let uu____7020 = tc_tycon env2 tc in
                                 (match uu____7020 with
                                  | (env3, tc1, tc_u, guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u in
                                      ((let uu____7047 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low in
                                        if uu____7047
                                        then
                                          let uu____7048 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1 in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7048
                                        else ());
                                       (let uu____7050 =
                                          let uu____7051 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g' in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7051 in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7050))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard) in
                    (match uu____6941 with
                     | (env2, tcs, g) ->
                         let uu____7097 =
                           FStar_List.fold_right
                             (fun se ->
                                fun uu____7119 ->
                                  match uu____7119 with
                                  | (datas2, g1) ->
                                      let uu____7138 =
                                        let uu____7143 = tc_data env2 tcs in
                                        uu____7143 se in
                                      (match uu____7138 with
                                       | (data, g') ->
                                           let uu____7160 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g' in
                                           ((data :: datas2), uu____7160)))
                             datas1 ([], g) in
                         (match uu____7097 with
                          | (datas2, g1) ->
                              let uu____7181 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7199 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs in
                                   (uu____7199, datas2)) in
                              (match uu____7181 with
                               | (tcs1, datas3) ->
                                   let sig_bndle =
                                     let uu____7231 =
                                       FStar_TypeChecker_Env.get_range env0 in
                                     let uu____7232 =
                                       FStar_List.collect
                                         (fun s ->
                                            s.FStar_Syntax_Syntax.sigattrs)
                                         ses in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_bundle
                                            ((FStar_List.append tcs1 datas3),
                                              lids));
                                       FStar_Syntax_Syntax.sigrng =
                                         uu____7231;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7232
                                     } in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l, univs2, binders, typ,
                                                 uu____7258, uu____7259)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7279 =
                                                    let uu____7284 =
                                                      let uu____7285 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected in
                                                      let uu____7286 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7285 uu____7286 in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7284) in
                                                  FStar_Errors.raise_error
                                                    uu____7279
                                                    se.FStar_Syntax_Syntax.sigrng in
                                                let uu____7287 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l in
                                                (match uu____7287 with
                                                 | FStar_Pervasives_Native.None
                                                     -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,
                                                      uu____7303)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7334 ->
                                                             let uu____7335 =
                                                               let uu____7342
                                                                 =
                                                                 let uu____7343
                                                                   =
                                                                   let uu____7358
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ in
                                                                   (binders,
                                                                    uu____7358) in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7343 in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7342 in
                                                             uu____7335
                                                               FStar_Pervasives_Native.None
                                                               se.FStar_Syntax_Syntax.sigrng in
                                                       (univs2, body) in
                                                     if
                                                       (FStar_List.length
                                                          univs2)
                                                         =
                                                         (FStar_List.length
                                                            (FStar_Pervasives_Native.fst
                                                               expected_typ1))
                                                     then
                                                       let uu____7382 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ in
                                                       (match uu____7382 with
                                                        | (uu____7387,
                                                           inferred) ->
                                                            let uu____7389 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1 in
                                                            (match uu____7389
                                                             with
                                                             | (uu____7394,
                                                                expected) ->
                                                                 let uu____7396
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected in
                                                                 if
                                                                   uu____7396
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7399 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))
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
                          let uu____7491 =
                            let uu____7498 =
                              let uu____7499 =
                                let uu____7506 =
                                  let uu____7509 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7509 in
                                (uu____7506, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7499 in
                            FStar_Syntax_Syntax.mk uu____7498 in
                          uu____7491 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7546 ->
                                  match uu____7546 with
                                  | (x, imp) ->
                                      let uu____7565 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7565, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7569 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7569 in
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
                               let uu____7590 =
                                 FStar_Ident.set_lid_range disc_name p in
                               FStar_Syntax_Syntax.fvar uu____7590
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None in
                             let uu____7591 =
                               let uu____7594 =
                                 let uu____7597 =
                                   let uu____7602 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7603 =
                                     let uu____7604 =
                                       let uu____7613 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7613 in
                                     [uu____7604] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7602
                                     uu____7603 in
                                 uu____7597 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7594 in
                             FStar_Syntax_Util.refine x uu____7591 in
                           let uu____7640 =
                             let uu___365_7641 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___365_7641.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___365_7641.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7640) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7658 =
                          FStar_List.map
                            (fun uu____7682 ->
                               match uu____7682 with
                               | (x, uu____7696) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7658 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7755 ->
                                match uu____7755 with
                                | (x, uu____7769) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))) in
                      let early_prims_inductive =
                        (let uu____7779 =
                           FStar_TypeChecker_Env.current_module env in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7779)
                          &&
                          (((tc.FStar_Ident.ident).FStar_Ident.idText =
                              "dtuple2")
                             ||
                             (FStar_List.existsb
                                (fun s ->
                                   s =
                                     (tc.FStar_Ident.ident).FStar_Ident.idText)
                                early_prims_inductives)) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             early_prims_inductive ||
                               (let uu____7792 =
                                  let uu____7793 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7793.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7792) in
                           let quals =
                             let uu____7797 =
                               FStar_List.filter
                                 (fun uu___351_7801 ->
                                    match uu___351_7801 with
                                    | FStar_Syntax_Syntax.Abstract ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.NoExtract -> true
                                    | FStar_Syntax_Syntax.Private -> true
                                    | uu____7802 -> false) iquals in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7797 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7837 =
                                 let uu____7838 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7838 in
                               FStar_Syntax_Syntax.mk_Total uu____7837 in
                             let uu____7839 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7839 in
                           let decl =
                             let uu____7843 =
                               FStar_Ident.range_of_lid discriminator_name in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7843;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             } in
                           (let uu____7845 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7845
                            then
                              let uu____7846 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7846
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
                                             fun uu____7897 ->
                                               match uu____7897 with
                                               | (x, imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7921 =
                                                       let uu____7924 =
                                                         let uu____7925 =
                                                           let uu____7932 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7932,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7925 in
                                                       pos uu____7924 in
                                                     (uu____7921, b)
                                                   else
                                                     (let uu____7938 =
                                                        let uu____7941 =
                                                          let uu____7942 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7942 in
                                                        pos uu____7941 in
                                                      (uu____7938, b)))) in
                                   let pat_true =
                                     let uu____7960 =
                                       let uu____7963 =
                                         let uu____7964 =
                                           let uu____7977 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____7977, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7964 in
                                       pos uu____7963 in
                                     (uu____7960,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____8011 =
                                       let uu____8014 =
                                         let uu____8015 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8015 in
                                       pos uu____8014 in
                                     (uu____8011,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____8029 =
                                     let uu____8036 =
                                       let uu____8037 =
                                         let uu____8060 =
                                           let uu____8077 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8092 =
                                             let uu____8109 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8109] in
                                           uu____8077 :: uu____8092 in
                                         (arg_exp, uu____8060) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8037 in
                                     FStar_Syntax_Syntax.mk uu____8036 in
                                   uu____8029 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____8188 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8188
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
                                let uu____8202 =
                                  let uu____8207 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____8207 in
                                let uu____8208 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                FStar_Syntax_Util.mk_letbinding uu____8202
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8208 [] FStar_Range.dummyRange in
                              let impl =
                                let uu____8214 =
                                  let uu____8215 =
                                    let uu____8222 =
                                      let uu____8225 =
                                        let uu____8226 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8226
                                          (fun fv ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8225] in
                                    ((false, [lb]), uu____8222) in
                                  FStar_Syntax_Syntax.Sig_let uu____8215 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8214;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____8238 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8238
                               then
                                 let uu____8239 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8239
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
                                fun uu____8309 ->
                                  match uu____8309 with
                                  | (a, uu____8317) ->
                                      let uu____8322 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8322 with
                                       | (field_name, uu____8328) ->
                                           let field_proj_tm =
                                             let uu____8330 =
                                               let uu____8331 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8331 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8330 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8356 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____8398 ->
                                    match uu____8398 with
                                    | (x, uu____8408) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8414 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8414 with
                                         | (field_name, uu____8422) ->
                                             let t =
                                               let uu____8426 =
                                                 let uu____8427 =
                                                   let uu____8430 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8430 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8427 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8426 in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8435 =
                                                    let uu____8436 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8436.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8435) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8452 =
                                                   FStar_List.filter
                                                     (fun uu___352_8456 ->
                                                        match uu___352_8456
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                            -> false
                                                        | uu____8457 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8452
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___353_8470 ->
                                                         match uu___353_8470
                                                         with
                                                         | FStar_Syntax_Syntax.NoExtract
                                                             -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                             -> true
                                                         | FStar_Syntax_Syntax.Private
                                                             -> true
                                                         | uu____8471 ->
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
                                               let uu____8479 =
                                                 FStar_Ident.range_of_lid
                                                   field_name in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8479;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               } in
                                             ((let uu____8481 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8481
                                               then
                                                 let uu____8482 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8482
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
                                                           fun uu____8528 ->
                                                             match uu____8528
                                                             with
                                                             | (x1, imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8552
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8552,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8568
                                                                    =
                                                                    let uu____8571
                                                                    =
                                                                    let uu____8572
                                                                    =
                                                                    let uu____8579
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8579,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8572 in
                                                                    pos
                                                                    uu____8571 in
                                                                    (uu____8568,
                                                                    b))
                                                                   else
                                                                    (let uu____8585
                                                                    =
                                                                    let uu____8588
                                                                    =
                                                                    let uu____8589
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8589 in
                                                                    pos
                                                                    uu____8588 in
                                                                    (uu____8585,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8607 =
                                                     let uu____8610 =
                                                       let uu____8611 =
                                                         let uu____8624 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8624,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8611 in
                                                     pos uu____8610 in
                                                   let uu____8633 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8607,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8633) in
                                                 let body =
                                                   let uu____8649 =
                                                     let uu____8656 =
                                                       let uu____8657 =
                                                         let uu____8680 =
                                                           let uu____8697 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8697] in
                                                         (arg_exp,
                                                           uu____8680) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8657 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8656 in
                                                   uu____8649
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8765 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8765
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
                                                   let uu____8776 =
                                                     let uu____8781 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8781 in
                                                   let uu____8782 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8776;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8782;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   } in
                                                 let impl =
                                                   let uu____8788 =
                                                     let uu____8789 =
                                                       let uu____8796 =
                                                         let uu____8799 =
                                                           let uu____8800 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8800
                                                             (fun fv ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8799] in
                                                       ((false, [lb]),
                                                         uu____8796) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8789 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8788;
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
                                                 (let uu____8812 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8812
                                                  then
                                                    let uu____8813 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8813
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8356 FStar_List.flatten in
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
              (constr_lid, uvs, t, typ_lid, n_typars, uu____8861) when
              let uu____8866 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid in
              Prims.op_Negation uu____8866 ->
              let uu____8867 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8867 with
               | (univ_opening, uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8889 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8889 with
                    | (formals, uu____8907) ->
                        let uu____8928 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1 ->
                                 let uu____8960 =
                                   let uu____8961 =
                                     let uu____8962 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8962 in
                                   FStar_Ident.lid_equals typ_lid uu____8961 in
                                 if uu____8960
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8981, uvs', tps, typ0,
                                        uu____8985, constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9002 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None ->
                              let uu____9043 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid in
                              if uu____9043
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng in
                        (match uu____8928 with
                         | (inductive_tps, typ0, should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____9070 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____9070 with
                              | (indices, uu____9088) ->
                                  let refine_domain =
                                    let uu____9110 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___354_9115 ->
                                              match uu___354_9115 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9116 -> true
                                              | uu____9125 -> false)) in
                                    if uu____9110
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___355_9135 =
                                      match uu___355_9135 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9138, fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9150 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____9151 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____9151 with
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
                                    let uu____9162 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____9162 with
                                    | (imp_tps, fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9245 ->
                                               fun uu____9246 ->
                                                 match (uu____9245,
                                                         uu____9246)
                                                 with
                                                 | ((x, uu____9272),
                                                    (x', uu____9274)) ->
                                                     let uu____9295 =
                                                       let uu____9302 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____9302) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9295) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9307 -> []