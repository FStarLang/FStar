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
          let uu____37 = FStar_Syntax_Subst.open_term tps k in
          (match uu____37 with
           | (tps1, k1) ->
               let uu____52 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____52 with
                | (tps2, env_tps, guard_params, us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____74 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____74 with
                     | (indices, t) ->
                         let uu____113 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____113 with
                          | (indices1, env', guard_indices, us') ->
                              let uu____134 =
                                let uu____139 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____139 with
                                | (t1, uu____151, g) ->
                                    let uu____153 =
                                      let uu____154 =
                                        let uu____155 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____155 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____154 in
                                    (t1, uu____153) in
                              (match uu____134 with
                               | (t1, guard) ->
                                   let k3 =
                                     let uu____169 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____169 in
                                   let uu____172 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____172 with
                                    | (t_type, u) ->
                                        ((let uu____188 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____188);
                                         (let t_tc =
                                            let uu____192 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____192 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____202 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              (uvs, t_tc) in
                                          (uu____202,
                                            (let uu___62_206 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, uvs, tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___62_206.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___62_206.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___62_206.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___62_206.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____211 -> failwith "impossible"
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
            let uu____274 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____313 ->
                     match uu____313 with
                     | (se1, u_tc) ->
                         let uu____328 =
                           let uu____329 =
                             let uu____330 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____330 in
                           FStar_Ident.lid_equals tc_lid uu____329 in
                         if uu____328
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____349, uu____350, tps, uu____352,
                                 uu____353, uu____354)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____393 ->
                                          match uu____393 with
                                          | (x, uu____405) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____409 =
                                  let uu____416 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____416, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____409
                            | uu____423 -> failwith "Impossible")
                         else FStar_Pervasives_Native.None) in
              match tps_u_opt with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None ->
                  if FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedDataConstructor,
                        "Unexpected data constructor")
                      se.FStar_Syntax_Syntax.sigrng in
            (match uu____274 with
             | (env1, tps, u_tc) ->
                 let uu____494 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____508 =
                     let uu____509 = FStar_Syntax_Subst.compress t1 in
                     uu____509.FStar_Syntax_Syntax.n in
                   match uu____508 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                       let uu____542 = FStar_Util.first_N ntps bs in
                       (match uu____542 with
                        | (uu____575, bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu____626 ->
                                        match uu____626 with
                                        | (x, uu____632) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____633 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____633)
                   | uu____634 -> ([], t1) in
                 (match uu____494 with
                  | (arguments, result) ->
                      ((let uu____668 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____668
                        then
                          let uu____669 = FStar_Syntax_Print.lid_to_string c in
                          let uu____670 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____671 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____669
                            uu____670 uu____671
                        else ());
                       (let uu____673 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____673 with
                        | (arguments1, env', us) ->
                            let uu____687 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____687 with
                             | (result1, res_lcomp) ->
                                 ((let uu____699 =
                                     let uu____700 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____700.FStar_Syntax_Syntax.n in
                                   match uu____699 with
                                   | FStar_Syntax_Syntax.Tm_type uu____703 ->
                                       ()
                                   | ty ->
                                       let uu____705 =
                                         let uu____710 =
                                           let uu____711 =
                                             FStar_Syntax_Print.term_to_string
                                               result1 in
                                           let uu____712 =
                                             FStar_Syntax_Print.term_to_string
                                               res_lcomp.FStar_Syntax_Syntax.res_typ in
                                           FStar_Util.format2
                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                             uu____711 uu____712 in
                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                           uu____710) in
                                       FStar_Errors.raise_error uu____705
                                         se.FStar_Syntax_Syntax.sigrng);
                                  (let uu____713 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____713 with
                                   | (head1, uu____733) ->
                                       ((let uu____755 =
                                           let uu____756 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____756.FStar_Syntax_Syntax.n in
                                         match uu____755 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             ({
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  fv;
                                                FStar_Syntax_Syntax.pos =
                                                  uu____760;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____761;_},
                                              uu____762)
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____768 ->
                                             let uu____769 =
                                               let uu____774 =
                                                 let uu____775 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     tc_lid in
                                                 let uu____776 =
                                                   FStar_Syntax_Print.term_to_string
                                                     head1 in
                                                 FStar_Util.format2
                                                   "Expected a constructor of type %s; got %s"
                                                   uu____775 uu____776 in
                                               (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                 uu____774) in
                                             FStar_Errors.raise_error
                                               uu____769
                                               se.FStar_Syntax_Syntax.sigrng);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g ->
                                                fun uu____789 ->
                                                  fun u_x ->
                                                    match uu____789 with
                                                    | (x, uu____796) ->
                                                        let uu____797 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____797)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____801 =
                                             let uu____808 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____838 ->
                                                       match uu____838 with
                                                       | (x, uu____850) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____808
                                               arguments1 in
                                           let uu____859 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____801
                                             uu____859 in
                                         ((let uu___63_863 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___63_863.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___63_863.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___63_863.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___63_863.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____870 -> failwith "impossible"
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
            let uu___64_927 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___64_927.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___64_927.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___64_927.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____937 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____937
           then
             let uu____938 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____938
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____966 ->
                     match uu____966 with
                     | (se, uu____972) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____973, uu____974, tps, k, uu____977,
                               uu____978)
                              ->
                              let uu____987 =
                                let uu____988 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____988 in
                              FStar_Syntax_Syntax.null_binder uu____987
                          | uu____995 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1011, uu____1012, t, uu____1014, uu____1015,
                          uu____1016)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1021 -> failwith "Impossible")) in
           let t =
             let uu____1025 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1025 in
           (let uu____1029 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1029
            then
              let uu____1030 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1030
            else ());
           (let uu____1032 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1032 with
            | (uvs, t1) ->
                ((let uu____1048 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1048
                  then
                    let uu____1049 =
                      let uu____1050 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1050
                        (FStar_String.concat ", ") in
                    let uu____1061 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1049 uu____1061
                  else ());
                 (let uu____1063 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1063 with
                  | (uvs1, t2) ->
                      let uu____1078 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1078 with
                       | (args, uu____1100) ->
                           let uu____1117 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1117 with
                            | (tc_types, data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1200 ->
                                       fun uu____1201 ->
                                         match (uu____1200, uu____1201) with
                                         | ((x, uu____1219),
                                            (se, uu____1221)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc, uu____1231, tps,
                                                   uu____1233, mutuals,
                                                   datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1245 =
                                                    let uu____1258 =
                                                      let uu____1259 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1259.FStar_Syntax_Syntax.n in
                                                    match uu____1258 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1, c) ->
                                                        let uu____1292 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1292
                                                         with
                                                         | (tps1, rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1364
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1387 -> ([], ty) in
                                                  (match uu____1245 with
                                                   | (tps1, t3) ->
                                                       let uu___65_1416 = se in
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
                                                           (uu___65_1416.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___65_1416.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___65_1416.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___65_1416.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1429 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1435 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40 ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___58_1477 ->
                                                match uu___58_1477 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc, uu____1485,
                                                       uu____1486,
                                                       uu____1487,
                                                       uu____1488,
                                                       uu____1489);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1490;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1491;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1492;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1493;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1508 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1531 ->
                                           fun d ->
                                             match uu____1531 with
                                             | (t3, uu____1538) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l, uu____1540,
                                                       uu____1541, tc, ntps,
                                                       mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1550 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1550
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___66_1551 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___66_1551.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___66_1551.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___66_1551.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___66_1551.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1554 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit) =
  fun env ->
    fun s ->
      let uu____1565 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1565
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____1573 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1573
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv, FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____1587 =
      let uu____1588 = FStar_Syntax_Subst.compress t in
      uu____1588.FStar_Syntax_Syntax.n in
    match uu____1587 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1609 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1614 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1707 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____1826 ->
               match uu____1826 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1861 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1861 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1707
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          (let uu____2153 =
             let uu____2154 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____2154 in
           debug_log env uu____2153);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____2157 =
              let uu____2158 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2158 in
            debug_log env uu____2157);
           (let uu____2161 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____2161) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2171 =
                  let uu____2172 = FStar_Syntax_Subst.compress btype1 in
                  uu____2172.FStar_Syntax_Syntax.n in
                match uu____2171 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let uu____2197 = try_get_fv t in
                    (match uu____2197 with
                     | (fv, us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2213 ->
                                 match uu____2213 with
                                 | (t1, uu____2219) ->
                                     let uu____2220 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2220) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2310 =
                        let uu____2311 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2311 in
                      if uu____2310
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2323 ->
                               match uu____2323 with
                               | (b, uu____2329) ->
                                   let uu____2330 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2330) sbs)
                           &&
                           ((let uu____2335 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2335 with
                             | (uu____2340, return_type) ->
                                 let uu____2342 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2342)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2411 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2413 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2416) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2491) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2565, branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2623 ->
                          match uu____2623 with
                          | (p, uu____2635, t) ->
                              let bs =
                                let uu____2648 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2648 in
                              let uu____2651 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2651 with
                               | (bs1, t1) ->
                                   let uu____2658 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2658)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2728, uu____2729)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2839 ->
                    ((let uu____2841 =
                        let uu____2842 =
                          let uu____2843 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2844 =
                            let uu____2845 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2845 in
                          Prims.strcat uu____2843 uu____2844 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2842 in
                      debug_log env uu____2841);
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
              (let uu____2887 =
                 let uu____2888 =
                   let uu____2889 =
                     let uu____2890 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2890 in
                   Prims.strcat ilid.FStar_Ident.str uu____2889 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2888 in
               debug_log env uu____2887);
              (let uu____2891 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2891 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2906 =
                        already_unfolded ilid args unfolded env in
                      if uu____2906
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2979 =
                            let uu____2980 =
                              let uu____2981 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2981
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2980 in
                          debug_log env uu____2979);
                         (let uu____2983 =
                            let uu____2984 = FStar_ST.op_Bang unfolded in
                            let uu____3084 =
                              let uu____3091 =
                                let uu____3104 =
                                  let uu____3113 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____3113 in
                                (ilid, uu____3104) in
                              [uu____3091] in
                            FStar_List.append uu____2984 uu____3084 in
                          FStar_ST.op_Colon_Equals unfolded uu____2983);
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
                  (let uu____3398 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____3398 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3420 ->
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
                         (let uu____3423 =
                            let uu____3424 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3424 in
                          debug_log env uu____3423);
                         (let uu____3425 =
                            let uu____3426 = FStar_Syntax_Subst.compress dt1 in
                            uu____3426.FStar_Syntax_Syntax.n in
                          match uu____3425 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3448 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____3448 with
                                | (ibs, dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____3497 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3497 dbs1 in
                                    let c1 =
                                      let uu____3501 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3501 c in
                                    let uu____3504 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____3504 with
                                     | (args1, uu____3532) ->
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
                                           let uu____3604 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3604 c1 in
                                         ((let uu____3612 =
                                             let uu____3613 =
                                               let uu____3614 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____3615 =
                                                 let uu____3616 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____3616 in
                                               Prims.strcat uu____3614
                                                 uu____3615 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3613 in
                                           debug_log env uu____3612);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3685 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3687 =
                                  let uu____3688 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____3688.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____3687
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
                   (let uu____3822 = try_get_fv t1 in
                    match uu____3822 with
                    | (fv, uu____3828) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  ((let uu____3849 =
                      let uu____3850 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3850 in
                    debug_log env uu____3849);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3852 =
                      FStar_List.fold_left
                        (fun uu____3869 ->
                           fun b ->
                             match uu____3869 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3890 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3959 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3890, uu____3959))) (true, env)
                        sbs1 in
                    match uu____3852 with | (b, uu____3969) -> b))
              | uu____3970 ->
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
              let uu____4057 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____4057 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____4079 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____4081 =
                      let uu____4082 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____4082 in
                    debug_log env uu____4081);
                   (let uu____4083 =
                      let uu____4084 = FStar_Syntax_Subst.compress dt in
                      uu____4084.FStar_Syntax_Syntax.n in
                    match uu____4083 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____4087 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4090) ->
                        let dbs1 =
                          let uu____4114 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____4114 in
                        let dbs2 =
                          let uu____4152 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____4152 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____4157 =
                            let uu____4158 =
                              let uu____4159 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____4159 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____4158 in
                          debug_log env uu____4157);
                         (let uu____4164 =
                            FStar_List.fold_left
                              (fun uu____4181 ->
                                 fun b ->
                                   match uu____4181 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____4202 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____4271 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____4202, uu____4271)))
                              (true, env) dbs3 in
                          match uu____4164 with | (b, uu____4281) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____4282, uu____4283) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4380 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____4406 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____4422, uu____4423, uu____4424) ->
            (lid, us, bs)
        | uu____4433 -> failwith "Impossible!" in
      match uu____4406 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____4443 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____4443 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____4466 =
                 let uu____4469 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____4469 in
               FStar_List.for_all
                 (fun d ->
                    let uu____4481 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4481
                      unfolded_inductives env2) uu____4466)
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4557, uu____4558, t, uu____4560, uu____4561, uu____4562) -> t
    | uu____4567 -> failwith "Impossible!"
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
          let uu____4586 =
            let uu____4587 = FStar_Syntax_Subst.compress dt1 in
            uu____4587.FStar_Syntax_Syntax.n in
          match uu____4586 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4591) ->
              let dbs1 =
                let uu____4615 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____4615 in
              let dbs2 =
                let uu____4653 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____4653 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____4668 =
                           let uu____4669 =
                             let uu____4670 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____4670] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4669 in
                         uu____4668 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____4675 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____4675 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____4683 =
                       let uu____4684 =
                         let uu____4685 =
                           let uu____4686 =
                             let uu____4687 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4687
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____4686 in
                         [uu____4685] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4684 in
                     uu____4683 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4704 -> FStar_Syntax_Util.t_true
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
                  (lid, uu____4776, uu____4777, uu____4778, uu____4779,
                   uu____4780)
                  -> lid
              | uu____4789 -> failwith "Impossible!" in
            let uu____4790 = acc in
            match uu____4790 with
            | (uu____4823, en, uu____4825, uu____4826) ->
                let uu____4839 =
                  FStar_TypeChecker_Util.get_optimized_haseq_axiom en ty
                    usubst us in
                (match uu____4839 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____4876 = acc in
                     (match uu____4876 with
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
                                     (uu____4938, uu____4939, uu____4940,
                                      t_lid, uu____4942, uu____4943)
                                     -> t_lid = lid
                                 | uu____4948 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____4955 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4955)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____4956 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____4959 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4956, uu____4959)))
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          fun tc_assume ->
            let us =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____5042, us, uu____5044, uu____5045, uu____5046,
                   uu____5047)
                  -> us
              | uu____5056 -> failwith "Impossible!" in
            let uu____5057 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____5057 with
            | (usubst, us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____5082 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____5082 with
                  | (axioms, env2, guard, cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____5140 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____5140 with
                       | (phi1, uu____5148) ->
                           ((let uu____5150 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____5150
                             then
                               let uu____5151 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____5151
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l ->
                                    fun uu____5168 ->
                                      match uu____5168 with
                                      | (lid, fml) ->
                                          let se =
                                            tc_assume env2 lid fml []
                                              FStar_Range.dummyRange in
                                          FStar_List.append l [se]) [] axioms in
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
                let uu____5220 =
                  let uu____5221 = FStar_Syntax_Subst.compress t in
                  uu____5221.FStar_Syntax_Syntax.n in
                match uu____5220 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____5228) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____5261 = is_mutual t' in
                    if uu____5261
                    then true
                    else
                      (let uu____5263 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____5263)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____5279) ->
                    is_mutual t'
                | uu____5284 -> false
              and exists_mutual uu___59_5285 =
                match uu___59_5285 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____5304 =
                let uu____5305 = FStar_Syntax_Subst.compress dt1 in
                uu____5305.FStar_Syntax_Syntax.n in
              match uu____5304 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5311) ->
                  let dbs1 =
                    let uu____5335 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____5335 in
                  let dbs2 =
                    let uu____5373 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____5373 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____5391 =
                               let uu____5392 =
                                 let uu____5393 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____5393] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5392 in
                             uu____5391 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____5397 = is_mutual sort in
                             if uu____5397
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____5407 =
                             let uu____5408 =
                               let uu____5409 =
                                 let uu____5410 =
                                   let uu____5411 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5411 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____5410 in
                               [uu____5409] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5408 in
                           uu____5407 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5428 -> acc
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
              let uu____5465 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____5487, bs, t, uu____5490, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5502 -> failwith "Impossible!" in
              match uu____5465 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____5525 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____5525 t in
                  let uu____5532 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____5532 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____5548 =
                           let uu____5549 = FStar_Syntax_Subst.compress t2 in
                           uu____5549.FStar_Syntax_Syntax.n in
                         match uu____5548 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5559) ->
                             ibs
                         | uu____5576 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____5583 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____5584 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5583
                           uu____5584 in
                       let ind1 =
                         let uu____5590 =
                           let uu____5591 =
                             FStar_List.map
                               (fun uu____5604 ->
                                  match uu____5604 with
                                  | (bv, aq) ->
                                      let uu____5615 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____5615, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5591 in
                         uu____5590 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____5621 =
                           let uu____5622 =
                             FStar_List.map
                               (fun uu____5635 ->
                                  match uu____5635 with
                                  | (bv, aq) ->
                                      let uu____5646 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____5646, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5622 in
                         uu____5621 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____5652 =
                           let uu____5653 =
                             let uu____5654 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____5654] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5653 in
                         uu____5652 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5668, uu____5669, uu____5670, t_lid,
                                   uu____5672, uu____5673)
                                  -> t_lid = lid
                              | uu____5678 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___67_5684 = fml in
                         let uu____5685 =
                           let uu____5686 =
                             let uu____5693 =
                               let uu____5694 =
                                 let uu____5705 =
                                   let uu____5708 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____5708] in
                                 [uu____5705] in
                               FStar_Syntax_Syntax.Meta_pattern uu____5694 in
                             (fml, uu____5693) in
                           FStar_Syntax_Syntax.Tm_meta uu____5686 in
                         {
                           FStar_Syntax_Syntax.n = uu____5685;
                           FStar_Syntax_Syntax.pos =
                             (uu___67_5684.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___67_5684.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____5721 =
                                  let uu____5722 =
                                    let uu____5723 =
                                      let uu____5724 =
                                        let uu____5725 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5725
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____5724 in
                                    [uu____5723] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5722 in
                                uu____5721 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____5750 =
                                  let uu____5751 =
                                    let uu____5752 =
                                      let uu____5753 =
                                        let uu____5754 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5754
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____5753 in
                                    [uu____5752] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5751 in
                                uu____5750 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2 in
                       FStar_Syntax_Util.mk_conj acc fml3)
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle ->
    fun tcs ->
      fun datas ->
        fun env0 ->
          fun tc_assume ->
            let mutuals =
              FStar_List.map
                (fun ty ->
                   match ty.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (lid, uu____5839, uu____5840, uu____5841, uu____5842,
                        uu____5843)
                       -> lid
                   | uu____5852 -> failwith "Impossible!") tcs in
            let uu____5853 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid, us, uu____5865, uu____5866, uu____5867, uu____5868)
                  -> (lid, us)
              | uu____5877 -> failwith "Impossible!" in
            match uu____5853 with
            | (lid, us) ->
                let uu____5886 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____5886 with
                 | (usubst, us1) ->
                     let fml =
                       FStar_List.fold_left
                         (unoptimized_haseq_ty datas mutuals usubst us1)
                         FStar_Syntax_Util.t_true tcs in
                     let env =
                       FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                     ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                        "haseq";
                      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                        env sig_bndle;
                      (let env1 =
                         FStar_TypeChecker_Env.push_univ_vars env us1 in
                       let se =
                         let uu____5913 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____5913 fml []
                           FStar_Range.dummyRange in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
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
          let uu____5959 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___60_5984 ->
                    match uu___60_5984 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5985;
                        FStar_Syntax_Syntax.sigrng = uu____5986;
                        FStar_Syntax_Syntax.sigquals = uu____5987;
                        FStar_Syntax_Syntax.sigmeta = uu____5988;
                        FStar_Syntax_Syntax.sigattrs = uu____5989;_} -> true
                    | uu____6010 -> false)) in
          match uu____5959 with
          | (tys, datas) ->
              ((let uu____6032 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___61_6041 ->
                          match uu___61_6041 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6042;
                              FStar_Syntax_Syntax.sigrng = uu____6043;
                              FStar_Syntax_Syntax.sigquals = uu____6044;
                              FStar_Syntax_Syntax.sigmeta = uu____6045;
                              FStar_Syntax_Syntax.sigattrs = uu____6046;_} ->
                              false
                          | uu____6065 -> true)) in
                if uu____6032
                then
                  let uu____6066 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6066
                else ());
               (let env0 = env in
                let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6075 =
                       let uu____6076 = FStar_List.hd tys in
                       uu____6076.FStar_Syntax_Syntax.sigel in
                     match uu____6075 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6079, uvs, uu____6081, uu____6082,
                          uu____6083, uu____6084)
                         -> uvs
                     | uu____6093 -> failwith "Impossible, can't happen!") in
                let uu____6096 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (tys, datas)
                  else
                    (let uu____6118 =
                       FStar_Syntax_Subst.univ_var_opening univs1 in
                     match uu____6118 with
                     | (subst1, univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid, uu____6154, bs, t, l1, l2) ->
                                      let uu____6167 =
                                        let uu____6184 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs in
                                        let uu____6185 =
                                          let uu____6186 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1 in
                                          FStar_Syntax_Subst.subst uu____6186
                                            t in
                                        (lid, univs2, uu____6184, uu____6185,
                                          l1, l2) in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6167
                                  | uu____6199 ->
                                      failwith "Impossible, can't happen" in
                                let uu___68_6200 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___68_6200.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___68_6200.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___68_6200.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___68_6200.FStar_Syntax_Syntax.sigattrs)
                                }) tys in
                         let datas1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid, uu____6210, t, lid_t, x, l) ->
                                      let uu____6219 =
                                        let uu____6234 =
                                          FStar_Syntax_Subst.subst subst1 t in
                                        (lid, univs2, uu____6234, lid_t, x,
                                          l) in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6219
                                  | uu____6239 ->
                                      failwith "Impossible, can't happen" in
                                let uu___69_6240 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___69_6240.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___69_6240.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___69_6240.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___69_6240.FStar_Syntax_Syntax.sigattrs)
                                }) datas in
                         (tys1, datas1)) in
                match uu____6096 with
                | (tys1, datas1) ->
                    let uu____6265 =
                      FStar_List.fold_right
                        (fun tc ->
                           fun uu____6304 ->
                             match uu____6304 with
                             | (env1, all_tcs, g) ->
                                 let uu____6344 = tc_tycon env1 tc in
                                 (match uu____6344 with
                                  | (env2, tc1, tc_u, guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u in
                                      ((let uu____6371 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Low in
                                        if uu____6371
                                        then
                                          let uu____6372 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1 in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____6372
                                        else ());
                                       (let uu____6374 =
                                          let uu____6375 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g' in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____6375 in
                                        (env2, ((tc1, tc_u) :: all_tcs),
                                          uu____6374))))) tys1
                        (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                    (match uu____6265 with
                     | (env1, tcs, g) ->
                         let uu____6421 =
                           FStar_List.fold_right
                             (fun se ->
                                fun uu____6443 ->
                                  match uu____6443 with
                                  | (datas2, g1) ->
                                      let uu____6462 =
                                        let uu____6467 = tc_data env1 tcs in
                                        uu____6467 se in
                                      (match uu____6462 with
                                       | (data, g') ->
                                           let uu____6482 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g' in
                                           ((data :: datas2), uu____6482)))
                             datas1 ([], g) in
                         (match uu____6421 with
                          | (datas2, g1) ->
                              let uu____6503 =
                                generalize_and_inst_within env0 g1 tcs datas2 in
                              (match uu____6503 with
                               | (tcs1, datas3) ->
                                   let sig_bndle =
                                     let uu____6533 =
                                       FStar_TypeChecker_Env.get_range env0 in
                                     let uu____6534 =
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
                                         uu____6533;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____6534
                                     } in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l, univs2, binders, typ,
                                                 uu____6560, uu____6561)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6577 =
                                                    let uu____6582 =
                                                      let uu____6583 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected in
                                                      let uu____6584 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6583 uu____6584 in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6582) in
                                                  FStar_Errors.raise_error
                                                    uu____6577
                                                    se.FStar_Syntax_Syntax.sigrng in
                                                let uu____6585 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l in
                                                (match uu____6585 with
                                                 | FStar_Pervasives_Native.None
                                                     -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,
                                                      uu____6601)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6622 ->
                                                             let uu____6623 =
                                                               let uu____6626
                                                                 =
                                                                 let uu____6627
                                                                   =
                                                                   let uu____6640
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ in
                                                                   (binders,
                                                                    uu____6640) in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6627 in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6626 in
                                                             uu____6623
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
                                                       let uu____6646 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ in
                                                       (match uu____6646 with
                                                        | (uu____6651,
                                                           inferred) ->
                                                            let uu____6653 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1 in
                                                            (match uu____6653
                                                             with
                                                             | (uu____6658,
                                                                expected) ->
                                                                 let uu____6660
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected in
                                                                 if
                                                                   uu____6660
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6663 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))