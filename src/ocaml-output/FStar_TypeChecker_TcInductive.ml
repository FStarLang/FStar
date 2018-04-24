open Prims
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
          let uu____42 = FStar_Syntax_Subst.univ_var_opening uvs in
          (match uu____42 with
           | (usubst, uvs1) ->
               let uu____69 =
                 let uu____76 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                 let uu____77 = FStar_Syntax_Subst.subst_binders usubst tps in
                 let uu____78 =
                   let uu____79 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst in
                   FStar_Syntax_Subst.subst uu____79 k in
                 (uu____76, uu____77, uu____78) in
               (match uu____69 with
                | (env1, tps1, k1) ->
                    let uu____97 = FStar_Syntax_Subst.open_term tps1 k1 in
                    (match uu____97 with
                     | (tps2, k2) ->
                         let uu____112 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2 in
                         (match uu____112 with
                          | (tps3, env_tps, guard_params, us) ->
                              let k3 =
                                FStar_TypeChecker_Normalize.unfold_whnf env1
                                  k2 in
                              let uu____134 =
                                FStar_Syntax_Util.arrow_formals k3 in
                              (match uu____134 with
                               | (indices, t) ->
                                   let uu____173 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices in
                                   (match uu____173 with
                                    | (indices1, env', guard_indices, us') ->
                                        let uu____194 =
                                          let uu____199 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t in
                                          match uu____199 with
                                          | (t1, uu____211, g) ->
                                              let uu____213 =
                                                let uu____214 =
                                                  let uu____215 =
                                                    FStar_TypeChecker_Rel.conj_guard
                                                      guard_indices g in
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    guard_params uu____215 in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____214 in
                                              (t1, uu____213) in
                                        (match uu____194 with
                                         | (t1, guard) ->
                                             let k4 =
                                               let uu____229 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1 in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____229 in
                                             let uu____232 =
                                               FStar_Syntax_Util.type_u () in
                                             (match uu____232 with
                                              | (t_type, u) ->
                                                  ((let uu____248 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env' t1 t_type in
                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                      env' uu____248);
                                                   (let usubst1 =
                                                      FStar_Syntax_Subst.univ_var_closing
                                                        uvs1 in
                                                    let t_tc =
                                                      let uu____255 =
                                                        let uu____262 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1) in
                                                        let uu____269 =
                                                          let uu____276 =
                                                            let uu____281 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1 in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____281 in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____276 in
                                                        FStar_List.append
                                                          uu____262 uu____269 in
                                                      let uu____292 =
                                                        let uu____295 =
                                                          let uu____296 =
                                                            let uu____301 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1 in
                                                            FStar_Syntax_Subst.subst
                                                              uu____301 in
                                                          FStar_All.pipe_right
                                                            t1 uu____296 in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____295 in
                                                      FStar_Syntax_Util.arrow
                                                        uu____255 uu____292 in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3 in
                                                    let k5 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k4 in
                                                    let uu____314 =
                                                      let uu____319 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4 in
                                                      let uu____320 =
                                                        let uu____321 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1 in
                                                        FStar_Syntax_Subst.subst
                                                          uu____321 k5 in
                                                      (uu____319, uu____320) in
                                                    match uu____314 with
                                                    | (tps5, k6) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.Delta_constant
                                                            FStar_Pervasives_Native.None in
                                                        let uu____339 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc) in
                                                        (uu____339,
                                                          (let uu___74_345 =
                                                             s in
                                                           {
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                  (tc, uvs1,
                                                                    tps5, k6,
                                                                    mutuals,
                                                                    data));
                                                             FStar_Syntax_Syntax.sigrng
                                                               =
                                                               (uu___74_345.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___74_345.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___74_345.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___74_345.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard)))))))))))
      | uu____352 -> failwith "impossible"
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
            let uu____412 = FStar_Syntax_Subst.univ_var_opening _uvs in
            (match uu____412 with
             | (usubst, _uvs1) ->
                 let uu____435 =
                   let uu____440 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1 in
                   let uu____441 = FStar_Syntax_Subst.subst usubst t in
                   (uu____440, uu____441) in
                 (match uu____435 with
                  | (env1, t1) ->
                      let uu____448 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____487 ->
                               match uu____487 with
                               | (se1, u_tc) ->
                                   let uu____502 =
                                     let uu____503 =
                                       let uu____504 =
                                         FStar_Syntax_Util.lid_of_sigelt se1 in
                                       FStar_Util.must uu____504 in
                                     FStar_Ident.lid_equals tc_lid uu____503 in
                                   if uu____502
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____523, uu____524, tps,
                                           uu____526, uu____527, uu____528)
                                          ->
                                          let tps1 =
                                            let uu____546 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst) in
                                            FStar_All.pipe_right uu____546
                                              (FStar_List.map
                                                 (fun uu____568 ->
                                                    match uu____568 with
                                                    | (x, uu____580) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag)))) in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1 in
                                          let uu____584 =
                                            let uu____591 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2 in
                                            (uu____591, tps2, u_tc) in
                                          FStar_Pervasives_Native.Some
                                            uu____584
                                      | uu____598 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None) in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None ->
                            let uu____639 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid in
                            if uu____639
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng in
                      (match uu____448 with
                       | (env2, tps, u_tc) ->
                           let uu____670 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1 in
                             let uu____684 =
                               let uu____685 = FStar_Syntax_Subst.compress t2 in
                               uu____685.FStar_Syntax_Syntax.n in
                             match uu____684 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                                 let uu____718 = FStar_Util.first_N ntps bs in
                                 (match uu____718 with
                                  | (uu____751, bs') ->
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
                                                fun uu____802 ->
                                                  match uu____802 with
                                                  | (x, uu____808) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x))) in
                                      let uu____809 =
                                        FStar_Syntax_Subst.subst subst1 t3 in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____809)
                             | uu____810 -> ([], t2) in
                           (match uu____670 with
                            | (arguments, result) ->
                                ((let uu____844 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low in
                                  if uu____844
                                  then
                                    let uu____845 =
                                      FStar_Syntax_Print.lid_to_string c in
                                    let uu____846 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments in
                                    let uu____847 =
                                      FStar_Syntax_Print.term_to_string
                                        result in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____845 uu____846 uu____847
                                  else ());
                                 (let uu____849 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments in
                                  match uu____849 with
                                  | (arguments1, env', us) ->
                                      let uu____863 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result in
                                      (match uu____863 with
                                       | (result1, res_lcomp) ->
                                           ((let uu____875 =
                                               let uu____876 =
                                                 FStar_Syntax_Subst.compress
                                                   res_lcomp.FStar_Syntax_Syntax.res_typ in
                                               uu____876.FStar_Syntax_Syntax.n in
                                             match uu____875 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____879 -> ()
                                             | ty ->
                                                 let uu____881 =
                                                   let uu____886 =
                                                     let uu____887 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1 in
                                                     let uu____888 =
                                                       FStar_Syntax_Print.term_to_string
                                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____887 uu____888 in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____886) in
                                                 FStar_Errors.raise_error
                                                   uu____881
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____889 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1 in
                                             match uu____889 with
                                             | (head1, uu____909) ->
                                                 let g_uvs =
                                                   let uu____931 =
                                                     let uu____932 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____932.FStar_Syntax_Syntax.n in
                                                   match uu____931 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____936;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____937;_},
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
                                                                  let uu____950
                                                                    =
                                                                    let uu____951
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    let uu____952
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'
                                                                    uu____951
                                                                    uu____952 in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g
                                                                    uu____950)
                                                           FStar_TypeChecker_Rel.trivial_guard
                                                           tuvs _uvs1
                                                       else
                                                         failwith
                                                           "Impossible: tc_datacon: length of annotated universes not same as instantiated ones"
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv tc_lid
                                                       ->
                                                       FStar_TypeChecker_Rel.trivial_guard
                                                   | uu____955 ->
                                                       let uu____956 =
                                                         let uu____961 =
                                                           let uu____962 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid in
                                                           let uu____963 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1 in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____962
                                                             uu____963 in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____961) in
                                                       FStar_Errors.raise_error
                                                         uu____956
                                                         se.FStar_Syntax_Syntax.sigrng in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g ->
                                                        fun uu____976 ->
                                                          fun u_x ->
                                                            match uu____976
                                                            with
                                                            | (x, uu____983)
                                                                ->
                                                                let uu____984
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g uu____984)
                                                     g_uvs arguments1 us in
                                                 let t2 =
                                                   let uu____988 =
                                                     let uu____995 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1025
                                                               ->
                                                               match uu____1025
                                                               with
                                                               | (x,
                                                                  uu____1037)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true))))) in
                                                     FStar_List.append
                                                       uu____995 arguments1 in
                                                   let uu____1046 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1 in
                                                   FStar_Syntax_Util.arrow
                                                     uu____988 uu____1046 in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2 in
                                                 ((let uu___75_1051 = se in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___75_1051.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___75_1051.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___75_1051.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___75_1051.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1056 -> failwith "impossible"
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
            let uu___76_1121 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___76_1121.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___76_1121.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___76_1121.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____1131 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____1131
           then
             let uu____1132 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1132
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1160 ->
                     match uu____1160 with
                     | (se, uu____1166) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1167, uu____1168, tps, k, uu____1171,
                               uu____1172)
                              ->
                              let uu____1181 =
                                let uu____1182 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1182 in
                              FStar_Syntax_Syntax.null_binder uu____1181
                          | uu____1189 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1205, uu____1206, t, uu____1208, uu____1209,
                          uu____1210)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1215 -> failwith "Impossible")) in
           let t =
             let uu____1219 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1219 in
           (let uu____1223 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1223
            then
              let uu____1224 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1224
            else ());
           (let uu____1226 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1226 with
            | (uvs, t1) ->
                ((let uu____1242 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1242
                  then
                    let uu____1243 =
                      let uu____1244 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1244
                        (FStar_String.concat ", ") in
                    let uu____1255 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1243 uu____1255
                  else ());
                 (let uu____1257 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1257 with
                  | (uvs1, t2) ->
                      let uu____1272 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1272 with
                       | (args, uu____1294) ->
                           let uu____1311 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1311 with
                            | (tc_types, data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1394 ->
                                       fun uu____1395 ->
                                         match (uu____1394, uu____1395) with
                                         | ((x, uu____1413),
                                            (se, uu____1415)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc, uu____1425, tps,
                                                   uu____1427, mutuals,
                                                   datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1439 =
                                                    let uu____1452 =
                                                      let uu____1453 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1453.FStar_Syntax_Syntax.n in
                                                    match uu____1452 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1, c) ->
                                                        let uu____1486 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1486
                                                         with
                                                         | (tps1, rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1558
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1581 -> ([], ty) in
                                                  (match uu____1439 with
                                                   | (tps1, t3) ->
                                                       let uu___77_1610 = se in
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
                                                           (uu___77_1610.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___77_1610.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___77_1610.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___77_1610.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1623 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1629 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_17 ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_17)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___65_1671 ->
                                                match uu___65_1671 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc, uu____1679,
                                                       uu____1680,
                                                       uu____1681,
                                                       uu____1682,
                                                       uu____1683);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1684;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1685;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1686;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1687;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1702 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1725 ->
                                           fun d ->
                                             match uu____1725 with
                                             | (t3, uu____1732) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l, uu____1734,
                                                       uu____1735, tc, ntps,
                                                       mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1744 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1744
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___78_1745 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___78_1745.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___78_1745.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___78_1745.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___78_1745.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1748 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env ->
    fun s ->
      let uu____1763 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1763
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____1775 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1775
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv, FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____1791 =
      let uu____1792 = FStar_Syntax_Subst.compress t in
      uu____1792.FStar_Syntax_Syntax.n in
    match uu____1791 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1813 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1818 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident, FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref[@@deriving show]
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid ->
    fun arrghs ->
      fun unfolded ->
        fun env ->
          let uu____1919 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____2042 ->
               match uu____2042 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2077 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____2077 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1919
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          (let uu____2417 =
             let uu____2418 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____2418 in
           debug_log env uu____2417);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____2421 =
              let uu____2422 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2422 in
            debug_log env uu____2421);
           (let uu____2425 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2425) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2436 =
                  let uu____2437 = FStar_Syntax_Subst.compress btype1 in
                  uu____2437.FStar_Syntax_Syntax.n in
                match uu____2436 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let uu____2462 = try_get_fv t in
                    (match uu____2462 with
                     | (fv, us) ->
                         let uu____2469 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid in
                         if uu____2469
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2479 ->
                                 match uu____2479 with
                                 | (t1, uu____2485) ->
                                     let uu____2486 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2486) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2576 =
                        let uu____2577 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2577 in
                      if uu____2576
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2589 ->
                               match uu____2589 with
                               | (b, uu____2595) ->
                                   let uu____2596 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2596) sbs)
                           &&
                           ((let uu____2601 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2601 with
                             | (uu____2606, return_type) ->
                                 let uu____2608 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2608)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2677 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2679 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2682) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2757) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2831, branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2889 ->
                          match uu____2889 with
                          | (p, uu____2901, t) ->
                              let bs =
                                let uu____2914 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2914 in
                              let uu____2917 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2917 with
                               | (bs1, t1) ->
                                   let uu____2924 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2924)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2994, uu____2995)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3105 ->
                    ((let uu____3107 =
                        let uu____3108 =
                          let uu____3109 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____3110 =
                            let uu____3111 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____3111 in
                          Prims.strcat uu____3109 uu____3110 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____3108 in
                      debug_log env uu____3107);
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
              (let uu____3153 =
                 let uu____3154 =
                   let uu____3155 =
                     let uu____3156 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____3156 in
                   Prims.strcat ilid.FStar_Ident.str uu____3155 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____3154 in
               debug_log env uu____3153);
              (let uu____3157 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____3157 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____3172 =
                        already_unfolded ilid args unfolded env in
                      if uu____3172
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____3245 =
                            let uu____3246 =
                              let uu____3247 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____3247
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____3246 in
                          debug_log env uu____3245);
                         (let uu____3249 =
                            let uu____3250 = FStar_ST.op_Bang unfolded in
                            let uu____3354 =
                              let uu____3361 =
                                let uu____3374 =
                                  let uu____3383 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3383 in
                                (ilid, uu____3374) in
                              [uu____3361] in
                            FStar_List.append uu____3250 uu____3354 in
                          FStar_ST.op_Colon_Equals unfolded uu____3249);
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
                  (let uu____3672 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3672 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3694 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.UnfoldUntil
                               FStar_Syntax_Syntax.Delta_constant;
                             FStar_TypeChecker_Normalize.Iota;
                             FStar_TypeChecker_Normalize.Zeta;
                             FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                             env dt in
                         (let uu____3697 =
                            let uu____3698 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3698 in
                          debug_log env uu____3697);
                         (let uu____3699 =
                            let uu____3700 = FStar_Syntax_Subst.compress dt1 in
                            uu____3700.FStar_Syntax_Syntax.n in
                          match uu____3699 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3722 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____3722 with
                                | (ibs, dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____3771 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3771 dbs1 in
                                    let c1 =
                                      let uu____3775 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3775 c in
                                    let uu____3778 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____3778 with
                                     | (args1, uu____3806) ->
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
                                           let uu____3878 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3878 c1 in
                                         ((let uu____3886 =
                                             let uu____3887 =
                                               let uu____3888 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____3889 =
                                                 let uu____3890 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____3890 in
                                               Prims.strcat uu____3888
                                                 uu____3889 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3887 in
                                           debug_log env uu____3886);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3959 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3961 =
                                  let uu____3962 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____3962.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____3961
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
                   (let uu____4096 = try_get_fv t1 in
                    match uu____4096 with
                    | (fv, uu____4102) ->
                        let uu____4103 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid in
                        if uu____4103
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  ((let uu____4124 =
                      let uu____4125 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____4125 in
                    debug_log env uu____4124);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____4127 =
                      FStar_List.fold_left
                        (fun uu____4144 ->
                           fun b ->
                             match uu____4144 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____4165 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____4234 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____4165, uu____4234))) (true, env)
                        sbs1 in
                    match uu____4127 with | (b, uu____4244) -> b))
              | uu____4245 ->
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
              let uu____4344 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____4344 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____4366 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____4368 =
                      let uu____4369 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____4369 in
                    debug_log env uu____4368);
                   (let uu____4370 =
                      let uu____4371 = FStar_Syntax_Subst.compress dt in
                      uu____4371.FStar_Syntax_Syntax.n in
                    match uu____4370 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____4374 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4377) ->
                        let dbs1 =
                          let uu____4401 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____4401 in
                        let dbs2 =
                          let uu____4439 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____4439 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____4444 =
                            let uu____4445 =
                              let uu____4446 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____4446 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____4445 in
                          debug_log env uu____4444);
                         (let uu____4451 =
                            FStar_List.fold_left
                              (fun uu____4468 ->
                                 fun b ->
                                   match uu____4468 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____4489 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____4558 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____4489, uu____4558)))
                              (true, env) dbs3 in
                          match uu____4451 with | (b, uu____4568) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____4569, uu____4570) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4667 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____4697 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____4713, uu____4714, uu____4715) ->
            (lid, us, bs)
        | uu____4724 -> failwith "Impossible!" in
      match uu____4697 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____4734 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____4734 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____4757 =
                 let uu____4760 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____4760 in
               FStar_List.for_all
                 (fun d ->
                    let uu____4772 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4772
                      unfolded_inductives env2) uu____4757)
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4850, uu____4851, t, uu____4853, uu____4854, uu____4855) -> t
    | uu____4860 -> failwith "Impossible!"
let (haseq_suffix : Prims.string) = "__uu___haseq"
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid ->
    let str = lid.FStar_Ident.str in
    let len = FStar_String.length str in
    let haseq_suffix_len = FStar_String.length haseq_suffix in
    (len > haseq_suffix_len) &&
      (let uu____4880 =
         let uu____4881 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len in
         FStar_String.compare uu____4881 haseq_suffix in
       uu____4880 = (Prims.parse_int "0"))
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid ->
    let uu____4901 =
      let uu____4904 =
        let uu____4907 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix) in
        [uu____4907] in
      FStar_List.append lid.FStar_Ident.ns uu____4904 in
    FStar_Ident.lid_of_ids uu____4901
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
          let uu____4952 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, uu____4966, bs, t, uu____4969, uu____4970) ->
                (lid, bs, t)
            | uu____4979 -> failwith "Impossible!" in
          match uu____4952 with
          | (lid, bs, t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
              let t1 =
                let uu____5001 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst in
                FStar_Syntax_Subst.subst uu____5001 t in
              let uu____5008 = FStar_Syntax_Subst.open_term bs1 t1 in
              (match uu____5008 with
               | (bs2, t2) ->
                   let ibs =
                     let uu____5032 =
                       let uu____5033 = FStar_Syntax_Subst.compress t2 in
                       uu____5033.FStar_Syntax_Syntax.n in
                     match uu____5032 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5043) -> ibs
                     | uu____5060 -> [] in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                   let ind =
                     let uu____5067 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None in
                     let uu____5068 =
                       FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name u)
                         us in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____5067 uu____5068 in
                   let ind1 =
                     let uu____5074 =
                       let uu____5079 =
                         FStar_List.map
                           (fun uu____5092 ->
                              match uu____5092 with
                              | (bv, aq) ->
                                  let uu____5103 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____5103, aq)) bs2 in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____5079 in
                     uu____5074 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let ind2 =
                     let uu____5109 =
                       let uu____5114 =
                         FStar_List.map
                           (fun uu____5127 ->
                              match uu____5127 with
                              | (bv, aq) ->
                                  let uu____5138 =
                                    FStar_Syntax_Syntax.bv_to_name bv in
                                  (uu____5138, aq)) ibs1 in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5114 in
                     uu____5109 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let haseq_ind =
                     let uu____5144 =
                       let uu____5149 =
                         let uu____5150 = FStar_Syntax_Syntax.as_arg ind2 in
                         [uu____5150] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____5149 in
                     uu____5144 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange in
                   let bs' =
                     FStar_List.filter
                       (fun b ->
                          let uu____5171 =
                            let uu____5172 = FStar_Syntax_Util.type_u () in
                            FStar_Pervasives_Native.fst uu____5172 in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____5171) bs2 in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3 ->
                          fun b ->
                            let uu____5183 =
                              let uu____5184 =
                                let uu____5189 =
                                  let uu____5190 =
                                    let uu____5191 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b) in
                                    FStar_Syntax_Syntax.as_arg uu____5191 in
                                  [uu____5190] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____5189 in
                              uu____5184 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange in
                            FStar_Syntax_Util.mk_conj t3 uu____5183)
                       FStar_Syntax_Util.t_true bs' in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                   let fml1 =
                     let uu___79_5198 = fml in
                     let uu____5199 =
                       let uu____5200 =
                         let uu____5207 =
                           let uu____5208 =
                             let uu____5219 =
                               let uu____5222 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind in
                               [uu____5222] in
                             [uu____5219] in
                           FStar_Syntax_Syntax.Meta_pattern uu____5208 in
                         (fml, uu____5207) in
                       FStar_Syntax_Syntax.Tm_meta uu____5200 in
                     {
                       FStar_Syntax_Syntax.n = uu____5199;
                       FStar_Syntax_Syntax.pos =
                         (uu___79_5198.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___79_5198.FStar_Syntax_Syntax.vars)
                     } in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____5235 =
                              let uu____5240 =
                                let uu____5241 =
                                  let uu____5242 =
                                    let uu____5243 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____5243 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____5242 in
                                [uu____5241] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____5240 in
                            uu____5235 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1 in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b ->
                          fun t3 ->
                            let uu____5268 =
                              let uu____5273 =
                                let uu____5274 =
                                  let uu____5275 =
                                    let uu____5276 =
                                      FStar_Syntax_Subst.close [b] t3 in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____5276 FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.as_arg uu____5275 in
                                [uu____5274] in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____5273 in
                            uu____5268 FStar_Pervasives_Native.None
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
          let uu____5320 =
            let uu____5321 = FStar_Syntax_Subst.compress dt1 in
            uu____5321.FStar_Syntax_Syntax.n in
          match uu____5320 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5325) ->
              let dbs1 =
                let uu____5349 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____5349 in
              let dbs2 =
                let uu____5387 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____5387 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____5402 =
                           let uu____5407 =
                             let uu____5408 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____5408] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5407 in
                         uu____5402 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____5413 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____5413 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____5421 =
                       let uu____5426 =
                         let uu____5427 =
                           let uu____5428 =
                             let uu____5429 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____5429
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____5428 in
                         [uu____5427] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____5426 in
                     uu____5421 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5446 -> FStar_Syntax_Util.t_true
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident, FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,
          FStar_TypeChecker_Env.env, FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple4 ->
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
                  (lid, uu____5528, uu____5529, uu____5530, uu____5531,
                   uu____5532)
                  -> lid
              | uu____5541 -> failwith "Impossible!" in
            let uu____5542 = acc in
            match uu____5542 with
            | (uu____5575, en, uu____5577, uu____5578) ->
                let uu____5591 = get_optimized_haseq_axiom en ty usubst us in
                (match uu____5591 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____5628 = acc in
                     (match uu____5628 with
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
                                     (uu____5690, uu____5691, uu____5692,
                                      t_lid, uu____5694, uu____5695)
                                     -> t_lid = lid
                                 | uu____5700 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____5707 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5707)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____5708 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____5711 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5708, uu____5711)))
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
                (uu____5770, us, uu____5772, uu____5773, uu____5774,
                 uu____5775)
                -> us
            | uu____5784 -> failwith "Impossible!" in
          let uu____5785 = FStar_Syntax_Subst.univ_var_opening us in
          match uu____5785 with
          | (usubst, us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                let uu____5810 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs in
                match uu____5810 with
                | (axioms, env2, guard, cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond in
                    let uu____5868 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                    (match uu____5868 with
                     | (phi1, uu____5876) ->
                         ((let uu____5878 =
                             FStar_TypeChecker_Env.should_verify env2 in
                           if uu____5878
                           then
                             let uu____5879 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1) in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____5879
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l ->
                                  fun uu____5896 ->
                                    match uu____5896 with
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
                let uu____5966 =
                  let uu____5967 = FStar_Syntax_Subst.compress t in
                  uu____5967.FStar_Syntax_Syntax.n in
                match uu____5966 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5974) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____6007 = is_mutual t' in
                    if uu____6007
                    then true
                    else
                      (let uu____6009 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____6009)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____6025) ->
                    is_mutual t'
                | uu____6030 -> false
              and exists_mutual uu___66_6031 =
                match uu___66_6031 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____6050 =
                let uu____6051 = FStar_Syntax_Subst.compress dt1 in
                uu____6051.FStar_Syntax_Syntax.n in
              match uu____6050 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____6057) ->
                  let dbs1 =
                    let uu____6081 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____6081 in
                  let dbs2 =
                    let uu____6119 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____6119 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____6137 =
                               let uu____6142 =
                                 let uu____6143 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____6143] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____6142 in
                             uu____6137 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____6147 = is_mutual sort in
                             if uu____6147
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____6157 =
                             let uu____6162 =
                               let uu____6163 =
                                 let uu____6164 =
                                   let uu____6165 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____6165 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____6164 in
                               [uu____6163] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____6162 in
                           uu____6157 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6182 -> acc
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
              let uu____6231 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____6253, bs, t, uu____6256, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6268 -> failwith "Impossible!" in
              match uu____6231 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____6291 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____6291 t in
                  let uu____6298 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____6298 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____6314 =
                           let uu____6315 = FStar_Syntax_Subst.compress t2 in
                           uu____6315.FStar_Syntax_Syntax.n in
                         match uu____6314 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____6325) ->
                             ibs
                         | uu____6342 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____6349 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____6350 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6349
                           uu____6350 in
                       let ind1 =
                         let uu____6356 =
                           let uu____6361 =
                             FStar_List.map
                               (fun uu____6374 ->
                                  match uu____6374 with
                                  | (bv, aq) ->
                                      let uu____6385 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6385, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6361 in
                         uu____6356 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____6391 =
                           let uu____6396 =
                             FStar_List.map
                               (fun uu____6409 ->
                                  match uu____6409 with
                                  | (bv, aq) ->
                                      let uu____6420 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____6420, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6396 in
                         uu____6391 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____6426 =
                           let uu____6431 =
                             let uu____6432 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____6432] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6431 in
                         uu____6426 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6446, uu____6447, uu____6448, t_lid,
                                   uu____6450, uu____6451)
                                  -> t_lid = lid
                              | uu____6456 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___80_6462 = fml in
                         let uu____6463 =
                           let uu____6464 =
                             let uu____6471 =
                               let uu____6472 =
                                 let uu____6483 =
                                   let uu____6486 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____6486] in
                                 [uu____6483] in
                               FStar_Syntax_Syntax.Meta_pattern uu____6472 in
                             (fml, uu____6471) in
                           FStar_Syntax_Syntax.Tm_meta uu____6464 in
                         {
                           FStar_Syntax_Syntax.n = uu____6463;
                           FStar_Syntax_Syntax.pos =
                             (uu___80_6462.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___80_6462.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6499 =
                                  let uu____6504 =
                                    let uu____6505 =
                                      let uu____6506 =
                                        let uu____6507 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6507
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6506 in
                                    [uu____6505] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6504 in
                                uu____6499 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____6532 =
                                  let uu____6537 =
                                    let uu____6538 =
                                      let uu____6539 =
                                        let uu____6540 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6540
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____6539 in
                                    [uu____6538] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6537 in
                                uu____6532 FStar_Pervasives_Native.None
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
                     (lid, uu____6601, uu____6602, uu____6603, uu____6604,
                      uu____6605)
                     -> lid
                 | uu____6614 -> failwith "Impossible!") tcs in
          let uu____6615 =
            let ty = FStar_List.hd tcs in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid, us, uu____6627, uu____6628, uu____6629, uu____6630) ->
                (lid, us)
            | uu____6639 -> failwith "Impossible!" in
          match uu____6615 with
          | (lid, us) ->
              let uu____6648 = FStar_Syntax_Subst.univ_var_opening us in
              (match uu____6648 with
               | (usubst, us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs in
                   let se =
                     let uu____6671 =
                       let uu____6672 =
                         let uu____6679 = get_haseq_axiom_lid lid in
                         (uu____6679, us1, fml) in
                       FStar_Syntax_Syntax.Sig_assume uu____6672 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6671;
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
          let uu____6734 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___67_6759 ->
                    match uu___67_6759 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6760;
                        FStar_Syntax_Syntax.sigrng = uu____6761;
                        FStar_Syntax_Syntax.sigquals = uu____6762;
                        FStar_Syntax_Syntax.sigmeta = uu____6763;
                        FStar_Syntax_Syntax.sigattrs = uu____6764;_} -> true
                    | uu____6785 -> false)) in
          match uu____6734 with
          | (tys, datas) ->
              ((let uu____6807 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___68_6816 ->
                          match uu___68_6816 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6817;
                              FStar_Syntax_Syntax.sigrng = uu____6818;
                              FStar_Syntax_Syntax.sigquals = uu____6819;
                              FStar_Syntax_Syntax.sigmeta = uu____6820;
                              FStar_Syntax_Syntax.sigattrs = uu____6821;_} ->
                              false
                          | uu____6840 -> true)) in
                if uu____6807
                then
                  let uu____6841 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6841
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6849 =
                       let uu____6850 = FStar_List.hd tys in
                       uu____6850.FStar_Syntax_Syntax.sigel in
                     match uu____6849 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6853, uvs, uu____6855, uu____6856,
                          uu____6857, uu____6858)
                         -> uvs
                     | uu____6867 -> failwith "Impossible, can't happen!") in
                let env0 = env in
                let uu____6871 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6897 =
                       FStar_Syntax_Subst.univ_var_opening univs1 in
                     match uu____6897 with
                     | (subst1, univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid, uu____6935, bs, t, l1, l2) ->
                                      let uu____6948 =
                                        let uu____6965 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs in
                                        let uu____6966 =
                                          let uu____6967 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1 in
                                          FStar_Syntax_Subst.subst uu____6967
                                            t in
                                        (lid, univs2, uu____6965, uu____6966,
                                          l1, l2) in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6948
                                  | uu____6980 ->
                                      failwith "Impossible, can't happen" in
                                let uu___81_6981 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___81_6981.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___81_6981.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___81_6981.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___81_6981.FStar_Syntax_Syntax.sigattrs)
                                }) tys in
                         let datas1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid, uu____6991, t, lid_t, x, l) ->
                                      let uu____7000 =
                                        let uu____7015 =
                                          FStar_Syntax_Subst.subst subst1 t in
                                        (lid, univs2, uu____7015, lid_t, x,
                                          l) in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____7000
                                  | uu____7020 ->
                                      failwith "Impossible, can't happen" in
                                let uu___82_7021 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___82_7021.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___82_7021.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___82_7021.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___82_7021.FStar_Syntax_Syntax.sigattrs)
                                }) datas in
                         let uu____7022 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2 in
                         (uu____7022, tys1, datas1)) in
                match uu____6871 with
                | (env1, tys1, datas1) ->
                    let uu____7048 =
                      FStar_List.fold_right
                        (fun tc ->
                           fun uu____7087 ->
                             match uu____7087 with
                             | (env2, all_tcs, g) ->
                                 let uu____7127 = tc_tycon env2 tc in
                                 (match uu____7127 with
                                  | (env3, tc1, tc_u, guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u in
                                      ((let uu____7154 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low in
                                        if uu____7154
                                        then
                                          let uu____7155 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1 in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7155
                                        else ());
                                       (let uu____7157 =
                                          let uu____7158 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g' in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____7158 in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7157))))) tys1
                        (env1, [], FStar_TypeChecker_Rel.trivial_guard) in
                    (match uu____7048 with
                     | (env2, tcs, g) ->
                         let uu____7204 =
                           FStar_List.fold_right
                             (fun se ->
                                fun uu____7226 ->
                                  match uu____7226 with
                                  | (datas2, g1) ->
                                      let uu____7245 =
                                        let uu____7250 = tc_data env2 tcs in
                                        uu____7250 se in
                                      (match uu____7245 with
                                       | (data, g') ->
                                           let uu____7267 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g' in
                                           ((data :: datas2), uu____7267)))
                             datas1 ([], g) in
                         (match uu____7204 with
                          | (datas2, g1) ->
                              let uu____7288 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7306 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs in
                                   (uu____7306, datas2)) in
                              (match uu____7288 with
                               | (tcs1, datas3) ->
                                   let sig_bndle =
                                     let uu____7338 =
                                       FStar_TypeChecker_Env.get_range env0 in
                                     let uu____7339 =
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
                                         uu____7338;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7339
                                     } in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l, univs2, binders, typ,
                                                 uu____7365, uu____7366)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7386 =
                                                    let uu____7391 =
                                                      let uu____7392 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected in
                                                      let uu____7393 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7392 uu____7393 in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7391) in
                                                  FStar_Errors.raise_error
                                                    uu____7386
                                                    se.FStar_Syntax_Syntax.sigrng in
                                                let uu____7394 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l in
                                                (match uu____7394 with
                                                 | FStar_Pervasives_Native.None
                                                     -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,
                                                      uu____7410)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7431 ->
                                                             let uu____7432 =
                                                               let uu____7439
                                                                 =
                                                                 let uu____7440
                                                                   =
                                                                   let uu____7453
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ in
                                                                   (binders,
                                                                    uu____7453) in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7440 in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7439 in
                                                             uu____7432
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
                                                       let uu____7459 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ in
                                                       (match uu____7459 with
                                                        | (uu____7464,
                                                           inferred) ->
                                                            let uu____7466 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1 in
                                                            (match uu____7466
                                                             with
                                                             | (uu____7471,
                                                                expected) ->
                                                                 let uu____7473
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected in
                                                                 if
                                                                   uu____7473
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7476 -> ()));
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
                          let uu____7568 =
                            let uu____7575 =
                              let uu____7576 =
                                let uu____7583 =
                                  let uu____7584 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7584 in
                                (uu____7583, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7576 in
                            FStar_Syntax_Syntax.mk uu____7575 in
                          uu____7568 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7625 ->
                                  match uu____7625 with
                                  | (x, imp) ->
                                      let uu____7636 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7636, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7638 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7638 in
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
                               let uu____7647 =
                                 FStar_Ident.set_lid_range disc_name p in
                               FStar_Syntax_Syntax.fvar uu____7647
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None in
                             let uu____7648 =
                               let uu____7649 =
                                 let uu____7650 =
                                   let uu____7655 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7656 =
                                     let uu____7657 =
                                       let uu____7658 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7658 in
                                     [uu____7657] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7655
                                     uu____7656 in
                                 uu____7650 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2p uu____7649 in
                             FStar_Syntax_Util.refine x uu____7648 in
                           let uu____7661 =
                             let uu___83_7662 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___83_7662.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___83_7662.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7661) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7677 =
                          FStar_List.map
                            (fun uu____7699 ->
                               match uu____7699 with
                               | (x, uu____7711) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7677 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7760 ->
                                match uu____7760 with
                                | (x, uu____7772) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))) in
                      let early_prims_inductive =
                        (let uu____7778 =
                           FStar_TypeChecker_Env.current_module env in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7778)
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
                               (let uu____7791 =
                                  let uu____7792 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7792.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7791) in
                           let quals =
                             let uu____7796 =
                               FStar_List.filter
                                 (fun uu___69_7800 ->
                                    match uu___69_7800 with
                                    | FStar_Syntax_Syntax.Abstract ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private -> true
                                    | uu____7801 -> false) iquals in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7796 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7822 =
                                 let uu____7823 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7823 in
                               FStar_Syntax_Syntax.mk_Total uu____7822 in
                             let uu____7824 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7824 in
                           let decl =
                             let uu____7826 =
                               FStar_Ident.range_of_lid discriminator_name in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7826;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             } in
                           (let uu____7828 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7828
                            then
                              let uu____7829 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7829
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
                                             fun uu____7882 ->
                                               match uu____7882 with
                                               | (x, imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7906 =
                                                       let uu____7909 =
                                                         let uu____7910 =
                                                           let uu____7917 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7917,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7910 in
                                                       pos uu____7909 in
                                                     (uu____7906, b)
                                                   else
                                                     (let uu____7921 =
                                                        let uu____7924 =
                                                          let uu____7925 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7925 in
                                                        pos uu____7924 in
                                                      (uu____7921, b)))) in
                                   let pat_true =
                                     let uu____7943 =
                                       let uu____7946 =
                                         let uu____7947 =
                                           let uu____7960 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____7960, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7947 in
                                       pos uu____7946 in
                                     (uu____7943,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____7994 =
                                       let uu____7997 =
                                         let uu____7998 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7998 in
                                       pos uu____7997 in
                                     (uu____7994,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____8010 =
                                     let uu____8017 =
                                       let uu____8018 =
                                         let uu____8041 =
                                           let uu____8044 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8045 =
                                             let uu____8048 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8048] in
                                           uu____8044 :: uu____8045 in
                                         (arg_exp, uu____8041) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8018 in
                                     FStar_Syntax_Syntax.mk uu____8017 in
                                   uu____8010 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____8055 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8055
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun in
                              let lb =
                                let uu____8063 =
                                  let uu____8068 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____8068 in
                                let uu____8069 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                FStar_Syntax_Util.mk_letbinding uu____8063
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8069 [] FStar_Range.dummyRange in
                              let impl =
                                let uu____8075 =
                                  let uu____8076 =
                                    let uu____8083 =
                                      let uu____8086 =
                                        let uu____8087 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8087
                                          (fun fv ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8086] in
                                    ((false, [lb]), uu____8083) in
                                  FStar_Syntax_Syntax.Sig_let uu____8076 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8075;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____8105 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8105
                               then
                                 let uu____8106 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8106
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
                                fun uu____8148 ->
                                  match uu____8148 with
                                  | (a, uu____8154) ->
                                      let uu____8155 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8155 with
                                       | (field_name, uu____8161) ->
                                           let field_proj_tm =
                                             let uu____8163 =
                                               let uu____8164 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8164 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8163 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8181 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____8213 ->
                                    match uu____8213 with
                                    | (x, uu____8221) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8223 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8223 with
                                         | (field_name, uu____8231) ->
                                             let t =
                                               let uu____8233 =
                                                 let uu____8234 =
                                                   let uu____8237 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8237 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8234 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8233 in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8240 =
                                                    let uu____8241 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8241.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8240) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8257 =
                                                   FStar_List.filter
                                                     (fun uu___70_8261 ->
                                                        match uu___70_8261
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                            -> false
                                                        | uu____8262 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8257
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___71_8275 ->
                                                         match uu___71_8275
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                             -> true
                                                         | FStar_Syntax_Syntax.Private
                                                             -> true
                                                         | uu____8276 ->
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
                                               let uu____8294 =
                                                 FStar_Ident.range_of_lid
                                                   field_name in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8294;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               } in
                                             ((let uu____8296 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8296
                                               then
                                                 let uu____8297 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8297
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
                                                           fun uu____8345 ->
                                                             match uu____8345
                                                             with
                                                             | (x1, imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8369
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8369,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8385
                                                                    =
                                                                    let uu____8388
                                                                    =
                                                                    let uu____8389
                                                                    =
                                                                    let uu____8396
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8396,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8389 in
                                                                    pos
                                                                    uu____8388 in
                                                                    (uu____8385,
                                                                    b))
                                                                   else
                                                                    (let uu____8400
                                                                    =
                                                                    let uu____8403
                                                                    =
                                                                    let uu____8404
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8404 in
                                                                    pos
                                                                    uu____8403 in
                                                                    (uu____8400,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8420 =
                                                     let uu____8423 =
                                                       let uu____8424 =
                                                         let uu____8437 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8437,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8424 in
                                                     pos uu____8423 in
                                                   let uu____8446 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8420,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8446) in
                                                 let body =
                                                   let uu____8458 =
                                                     let uu____8465 =
                                                       let uu____8466 =
                                                         let uu____8489 =
                                                           let uu____8492 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8492] in
                                                         (arg_exp,
                                                           uu____8489) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8466 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8465 in
                                                   uu____8458
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8500 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8500
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun in
                                                 let lb =
                                                   let uu____8507 =
                                                     let uu____8512 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8512 in
                                                   let uu____8513 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8507;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8513;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   } in
                                                 let impl =
                                                   let uu____8519 =
                                                     let uu____8520 =
                                                       let uu____8527 =
                                                         let uu____8530 =
                                                           let uu____8531 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8531
                                                             (fun fv ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8530] in
                                                       ((false, [lb]),
                                                         uu____8527) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8520 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8519;
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
                                                 (let uu____8549 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8549
                                                  then
                                                    let uu____8550 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8550
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8181 FStar_List.flatten in
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
              (constr_lid, uvs, t, typ_lid, n_typars, uu____8598) when
              let uu____8603 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid in
              Prims.op_Negation uu____8603 ->
              let uu____8604 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8604 with
               | (univ_opening, uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8626 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8626 with
                    | (formals, uu____8642) ->
                        let uu____8659 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1 ->
                                 let uu____8691 =
                                   let uu____8692 =
                                     let uu____8693 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8693 in
                                   FStar_Ident.lid_equals typ_lid uu____8692 in
                                 if uu____8691
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8712, uvs', tps, typ0,
                                        uu____8716, constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8733 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None ->
                              let uu____8774 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid in
                              if uu____8774
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng in
                        (match uu____8659 with
                         | (inductive_tps, typ0, should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8807 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8807 with
                              | (indices, uu____8823) ->
                                  let refine_domain =
                                    let uu____8841 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___72_8846 ->
                                              match uu___72_8846 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8847 -> true
                                              | uu____8856 -> false)) in
                                    if uu____8841
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___73_8866 =
                                      match uu___73_8866 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8869, fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8881 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8882 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8882 with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals in
                                  let fields =
                                    let uu____8893 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8893 with
                                    | (imp_tps, fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8958 ->
                                               fun uu____8959 ->
                                                 match (uu____8958,
                                                         uu____8959)
                                                 with
                                                 | ((x, uu____8977),
                                                    (x', uu____8979)) ->
                                                     let uu____8988 =
                                                       let uu____8995 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8995) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8988) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8996 -> []