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
                                            (let uu___59_206 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, uvs, tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___59_206.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___59_206.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___59_206.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___59_206.FStar_Syntax_Syntax.sigattrs)
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
            let uu____268 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____307 ->
                     match uu____307 with
                     | (se1, u_tc) ->
                         let uu____322 =
                           let uu____323 =
                             let uu____324 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____324 in
                           FStar_Ident.lid_equals tc_lid uu____323 in
                         if uu____322
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____343, uu____344, tps, uu____346,
                                 uu____347, uu____348)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____387 ->
                                          match uu____387 with
                                          | (x, uu____399) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____403 =
                                  let uu____410 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____410, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____403
                            | uu____417 -> failwith "Impossible")
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
            (match uu____268 with
             | (env1, tps, u_tc) ->
                 let uu____488 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____502 =
                     let uu____503 = FStar_Syntax_Subst.compress t1 in
                     uu____503.FStar_Syntax_Syntax.n in
                   match uu____502 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, res) ->
                       let uu____536 = FStar_Util.first_N ntps bs in
                       (match uu____536 with
                        | (uu____569, bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i ->
                                      fun uu____620 ->
                                        match uu____620 with
                                        | (x, uu____626) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____627 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____627)
                   | uu____628 -> ([], t1) in
                 (match uu____488 with
                  | (arguments, result) ->
                      ((let uu____662 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____662
                        then
                          let uu____663 = FStar_Syntax_Print.lid_to_string c in
                          let uu____664 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____665 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____663
                            uu____664 uu____665
                        else ());
                       (let uu____667 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____667 with
                        | (arguments1, env', us) ->
                            let uu____681 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____681 with
                             | (result1, res_lcomp) ->
                                 ((let uu____693 =
                                     let uu____694 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____694.FStar_Syntax_Syntax.n in
                                   match uu____693 with
                                   | FStar_Syntax_Syntax.Tm_type uu____697 ->
                                       ()
                                   | ty ->
                                       let uu____699 =
                                         let uu____704 =
                                           let uu____705 =
                                             FStar_Syntax_Print.term_to_string
                                               result1 in
                                           let uu____706 =
                                             FStar_Syntax_Print.term_to_string
                                               res_lcomp.FStar_Syntax_Syntax.res_typ in
                                           FStar_Util.format2
                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                             uu____705 uu____706 in
                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                           uu____704) in
                                       FStar_Errors.raise_error uu____699
                                         se.FStar_Syntax_Syntax.sigrng);
                                  (let uu____707 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____707 with
                                   | (head1, uu____727) ->
                                       ((let uu____749 =
                                           let uu____750 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____750.FStar_Syntax_Syntax.n in
                                         match uu____749 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             ({
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  fv;
                                                FStar_Syntax_Syntax.pos =
                                                  uu____754;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____755;_},
                                              uu____756)
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____762 ->
                                             let uu____763 =
                                               let uu____768 =
                                                 let uu____769 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     tc_lid in
                                                 let uu____770 =
                                                   FStar_Syntax_Print.term_to_string
                                                     head1 in
                                                 FStar_Util.format2
                                                   "Expected a constructor of type %s; got %s"
                                                   uu____769 uu____770 in
                                               (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                 uu____768) in
                                             FStar_Errors.raise_error
                                               uu____763
                                               se.FStar_Syntax_Syntax.sigrng);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g ->
                                                fun uu____783 ->
                                                  fun u_x ->
                                                    match uu____783 with
                                                    | (x, uu____790) ->
                                                        let uu____791 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____791)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____795 =
                                             let uu____802 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____832 ->
                                                       match uu____832 with
                                                       | (x, uu____844) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____802
                                               arguments1 in
                                           let uu____853 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____795
                                             uu____853 in
                                         ((let uu___60_857 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___60_857.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___60_857.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___60_857.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___60_857.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____864 -> failwith "impossible"
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
            let uu___61_921 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___61_921.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___61_921.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___61_921.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____931 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____931
           then
             let uu____932 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____932
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____960 ->
                     match uu____960 with
                     | (se, uu____966) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____967, uu____968, tps, k, uu____971,
                               uu____972)
                              ->
                              let uu____981 =
                                let uu____982 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____982 in
                              FStar_Syntax_Syntax.null_binder uu____981
                          | uu____989 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1005, uu____1006, t, uu____1008, uu____1009,
                          uu____1010)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1015 -> failwith "Impossible")) in
           let t =
             let uu____1019 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1019 in
           (let uu____1023 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1023
            then
              let uu____1024 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1024
            else ());
           (let uu____1026 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1026 with
            | (uvs, t1) ->
                ((let uu____1042 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1042
                  then
                    let uu____1043 =
                      let uu____1044 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1044
                        (FStar_String.concat ", ") in
                    let uu____1055 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1043 uu____1055
                  else ());
                 (let uu____1057 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1057 with
                  | (uvs1, t2) ->
                      let uu____1072 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1072 with
                       | (args, uu____1094) ->
                           let uu____1111 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1111 with
                            | (tc_types, data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1194 ->
                                       fun uu____1195 ->
                                         match (uu____1194, uu____1195) with
                                         | ((x, uu____1213),
                                            (se, uu____1215)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc, uu____1225, tps,
                                                   uu____1227, mutuals,
                                                   datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1239 =
                                                    let uu____1252 =
                                                      let uu____1253 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1253.FStar_Syntax_Syntax.n in
                                                    match uu____1252 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1, c) ->
                                                        let uu____1286 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1286
                                                         with
                                                         | (tps1, rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1358
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1381 -> ([], ty) in
                                                  (match uu____1239 with
                                                   | (tps1, t3) ->
                                                       let uu___62_1410 = se in
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
                                                           (uu___62_1410.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___62_1410.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___62_1410.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___62_1410.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1423 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1429 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40 ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___55_1471 ->
                                                match uu___55_1471 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc, uu____1479,
                                                       uu____1480,
                                                       uu____1481,
                                                       uu____1482,
                                                       uu____1483);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1484;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1485;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1486;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1487;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1502 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1525 ->
                                           fun d ->
                                             match uu____1525 with
                                             | (t3, uu____1532) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l, uu____1534,
                                                       uu____1535, tc, ntps,
                                                       mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1544 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1544
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___63_1545 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___63_1545.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___63_1545.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___63_1545.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___63_1545.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1548 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit) =
  fun env ->
    fun s ->
      let uu____1559 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1559
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu____1567 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1567
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv, FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let uu____1581 =
      let uu____1582 = FStar_Syntax_Subst.compress t in
      uu____1582.FStar_Syntax_Syntax.n in
    match uu____1581 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1603 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1608 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1653 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____1718 ->
               match uu____1718 with
               | (lid, l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1753 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1753 in
                      FStar_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1653
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid ->
    fun btype ->
      fun unfolded ->
        fun env ->
          (let uu____1925 =
             let uu____1926 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1926 in
           debug_log env uu____1925);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1929 =
              let uu____1930 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1930 in
            debug_log env uu____1929);
           (let uu____1933 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1933) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1943 =
                  let uu____1944 = FStar_Syntax_Subst.compress btype1 in
                  uu____1944.FStar_Syntax_Syntax.n in
                match uu____1943 with
                | FStar_Syntax_Syntax.Tm_app (t, args) ->
                    let uu____1969 = try_get_fv t in
                    (match uu____1969 with
                     | (fv, us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1985 ->
                                 match uu____1985 with
                                 | (t1, uu____1991) ->
                                     let uu____1992 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1992) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2034 =
                        let uu____2035 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2035 in
                      if uu____2034
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2047 ->
                               match uu____2047 with
                               | (b, uu____2053) ->
                                   let uu____2054 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2054) sbs)
                           &&
                           ((let uu____2059 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2059 with
                             | (uu____2064, return_type) ->
                                 let uu____2066 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2066)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2087 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2089 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t, uu____2092) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv, uu____2119) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2145, branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2203 ->
                          match uu____2203 with
                          | (p, uu____2215, t) ->
                              let bs =
                                let uu____2228 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2228 in
                              let uu____2231 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2231 with
                               | (bs1, t1) ->
                                   let uu____2238 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2238)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t, uu____2260, uu____2261)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2323 ->
                    ((let uu____2325 =
                        let uu____2326 =
                          let uu____2327 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2328 =
                            let uu____2329 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2329 in
                          Prims.strcat uu____2327 uu____2328 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2326 in
                      debug_log env uu____2325);
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
              (let uu____2347 =
                 let uu____2348 =
                   let uu____2349 =
                     let uu____2350 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2350 in
                   Prims.strcat ilid.FStar_Ident.str uu____2349 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2348 in
               debug_log env uu____2347);
              (let uu____2351 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2351 with
               | (b, idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2366 =
                        already_unfolded ilid args unfolded env in
                      if uu____2366
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2391 =
                            let uu____2392 =
                              let uu____2393 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2393
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2392 in
                          debug_log env uu____2391);
                         (let uu____2395 =
                            let uu____2396 = FStar_ST.op_Bang unfolded in
                            let uu____2442 =
                              let uu____2449 =
                                let uu____2462 =
                                  let uu____2471 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2471 in
                                (ilid, uu____2462) in
                              [uu____2449] in
                            FStar_List.append uu____2396 uu____2442 in
                          FStar_ST.op_Colon_Equals unfolded uu____2395);
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
                  (let uu____2630 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2630 with
                   | (univ_unif_vars, dt) ->
                       (FStar_List.iter2
                          (fun u' ->
                             fun u ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2652 ->
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
                         (let uu____2655 =
                            let uu____2656 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2656 in
                          debug_log env uu____2655);
                         (let uu____2657 =
                            let uu____2658 = FStar_Syntax_Subst.compress dt1 in
                            uu____2658.FStar_Syntax_Syntax.n in
                          match uu____2657 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs, c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2680 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2680 with
                                | (ibs, dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2729 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2729 dbs1 in
                                    let c1 =
                                      let uu____2733 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2733 c in
                                    let uu____2736 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2736 with
                                     | (args1, uu____2764) ->
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
                                           let uu____2836 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2836 c1 in
                                         ((let uu____2844 =
                                             let uu____2845 =
                                               let uu____2846 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2847 =
                                                 let uu____2848 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2848 in
                                               Prims.strcat uu____2846
                                                 uu____2847 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2845 in
                                           debug_log env uu____2844);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2869 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2871 =
                                  let uu____2872 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2872.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2871
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
                   (let uu____2934 = try_get_fv t1 in
                    match uu____2934 with
                    | (fv, uu____2940) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs, c) ->
                  ((let uu____2961 =
                      let uu____2962 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2962 in
                    debug_log env uu____2961);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____2964 =
                      FStar_List.fold_left
                        (fun uu____2981 ->
                           fun b ->
                             match uu____2981 with
                             | (r, env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3002 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3023 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3002, uu____3023))) (true, env)
                        sbs1 in
                    match uu____2964 with | (b, uu____3033) -> b))
              | uu____3034 ->
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
              let uu____3073 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3073 with
              | (univ_unif_vars, dt) ->
                  (FStar_List.iter2
                     (fun u' ->
                        fun u ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3095 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3097 =
                      let uu____3098 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____3098 in
                    debug_log env uu____3097);
                   (let uu____3099 =
                      let uu____3100 = FStar_Syntax_Subst.compress dt in
                      uu____3100.FStar_Syntax_Syntax.n in
                    match uu____3099 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3103 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3106) ->
                        let dbs1 =
                          let uu____3130 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3130 in
                        let dbs2 =
                          let uu____3168 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3168 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3173 =
                            let uu____3174 =
                              let uu____3175 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____3175 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3174 in
                          debug_log env uu____3173);
                         (let uu____3180 =
                            FStar_List.fold_left
                              (fun uu____3197 ->
                                 fun b ->
                                   match uu____3197 with
                                   | (r, env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3218 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3239 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3218, uu____3239)))
                              (true, env) dbs3 in
                          match uu____3180 with | (b, uu____3249) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3250, uu____3251) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t, univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3300 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty ->
    fun env ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3326 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, us, bs, uu____3342, uu____3343, uu____3344) ->
            (lid, us, bs)
        | uu____3353 -> failwith "Impossible!" in
      match uu____3326 with
      | (ty_lid, ty_us, ty_bs) ->
          let uu____3363 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3363 with
           | (ty_usubst, ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3386 =
                 let uu____3389 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3389 in
               FStar_List.for_all
                 (fun d ->
                    let uu____3401 =
                      FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3401
                      unfolded_inductives env2) uu____3386)
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3429, uu____3430, t, uu____3432, uu____3433, uu____3434) -> t
    | uu____3439 -> failwith "Impossible!"
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
          let uu____3458 =
            let uu____3459 = FStar_Syntax_Subst.compress dt1 in
            uu____3459.FStar_Syntax_Syntax.n in
          match uu____3458 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3463) ->
              let dbs1 =
                let uu____3487 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3487 in
              let dbs2 =
                let uu____3525 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3525 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t ->
                     fun b ->
                       let haseq_b =
                         let uu____3540 =
                           let uu____3541 =
                             let uu____3542 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3542] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3541 in
                         uu____3540 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3547 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3547 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b ->
                   fun t ->
                     let uu____3555 =
                       let uu____3556 =
                         let uu____3557 =
                           let uu____3558 =
                             let uu____3559 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3559
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3558 in
                         [uu____3557] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3556 in
                     uu____3555 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3576 -> FStar_Syntax_Util.t_true
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
                  (lid, uu____3648, uu____3649, uu____3650, uu____3651,
                   uu____3652)
                  -> lid
              | uu____3661 -> failwith "Impossible!" in
            let uu____3662 = acc in
            match uu____3662 with
            | (uu____3695, en, uu____3697, uu____3698) ->
                let uu____3711 =
                  FStar_TypeChecker_Util.get_optimized_haseq_axiom en ty
                    usubst us in
                (match uu____3711 with
                 | (axiom_lid, fml, bs, ibs, haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml in
                     let uu____3748 = acc in
                     (match uu____3748 with
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
                                     (uu____3810, uu____3811, uu____3812,
                                      t_lid, uu____3814, uu____3815)
                                     -> t_lid = lid
                                 | uu____3820 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1 ->
                                 fun d ->
                                   let uu____3827 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs in
                                   FStar_Syntax_Util.mk_conj acc1 uu____3827)
                              FStar_Syntax_Util.t_true t_datas in
                          let uu____3828 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____3831 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____3828, uu____3831)))
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
                  (uu____3914, us, uu____3916, uu____3917, uu____3918,
                   uu____3919)
                  -> us
              | uu____3928 -> failwith "Impossible!" in
            let uu____3929 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____3929 with
            | (usubst, us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____3954 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____3954 with
                  | (axioms, env2, guard, cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____4012 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____4012 with
                       | (phi1, uu____4020) ->
                           ((let uu____4022 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____4022
                             then
                               let uu____4023 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4023
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l ->
                                    fun uu____4040 ->
                                      match uu____4040 with
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
                let uu____4092 =
                  let uu____4093 = FStar_Syntax_Subst.compress t in
                  uu____4093.FStar_Syntax_Syntax.n in
                match uu____4092 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t', uu____4100) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv, t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t', args) ->
                    let uu____4133 = is_mutual t' in
                    if uu____4133
                    then true
                    else
                      (let uu____4135 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4135)
                | FStar_Syntax_Syntax.Tm_meta (t', uu____4151) ->
                    is_mutual t'
                | uu____4156 -> false
              and exists_mutual uu___56_4157 =
                match uu___56_4157 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4176 =
                let uu____4177 = FStar_Syntax_Subst.compress dt1 in
                uu____4177.FStar_Syntax_Syntax.n in
              match uu____4176 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4183) ->
                  let dbs1 =
                    let uu____4207 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4207 in
                  let dbs2 =
                    let uu____4245 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4245 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t ->
                         fun b ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4263 =
                               let uu____4264 =
                                 let uu____4265 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4265] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4264 in
                             uu____4263 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4269 = is_mutual sort in
                             if uu____4269
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b ->
                         fun t ->
                           let uu____4279 =
                             let uu____4280 =
                               let uu____4281 =
                                 let uu____4282 =
                                   let uu____4283 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4283 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4282 in
                               [uu____4281] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4280 in
                           uu____4279 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4300 -> acc
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
              let uu____4337 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid, uu____4359, bs, t, uu____4362, d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4374 -> failwith "Impossible!" in
              match uu____4337 with
              | (lid, bs, t, d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____4397 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____4397 t in
                  let uu____4404 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____4404 with
                   | (bs2, t2) ->
                       let ibs =
                         let uu____4420 =
                           let uu____4421 = FStar_Syntax_Subst.compress t2 in
                           uu____4421.FStar_Syntax_Syntax.n in
                         match uu____4420 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4431) ->
                             ibs
                         | uu____4448 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____4455 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____4456 =
                           FStar_List.map
                             (fun u -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4455
                           uu____4456 in
                       let ind1 =
                         let uu____4462 =
                           let uu____4463 =
                             FStar_List.map
                               (fun uu____4476 ->
                                  match uu____4476 with
                                  | (bv, aq) ->
                                      let uu____4487 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4487, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4463 in
                         uu____4462 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____4493 =
                           let uu____4494 =
                             FStar_List.map
                               (fun uu____4507 ->
                                  match uu____4507 with
                                  | (bv, aq) ->
                                      let uu____4518 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4518, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4494 in
                         uu____4493 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____4524 =
                           let uu____4525 =
                             let uu____4526 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____4526] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4525 in
                         uu____4524 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4540, uu____4541, uu____4542, t_lid,
                                   uu____4544, uu____4545)
                                  -> t_lid = lid
                              | uu____4550 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___64_4556 = fml in
                         let uu____4557 =
                           let uu____4558 =
                             let uu____4565 =
                               let uu____4566 =
                                 let uu____4577 =
                                   let uu____4580 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____4580] in
                                 [uu____4577] in
                               FStar_Syntax_Syntax.Meta_pattern uu____4566 in
                             (fml, uu____4565) in
                           FStar_Syntax_Syntax.Tm_meta uu____4558 in
                         {
                           FStar_Syntax_Syntax.n = uu____4557;
                           FStar_Syntax_Syntax.pos =
                             (uu___64_4556.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___64_4556.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____4593 =
                                  let uu____4594 =
                                    let uu____4595 =
                                      let uu____4596 =
                                        let uu____4597 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4597
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4596 in
                                    [uu____4595] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4594 in
                                uu____4593 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b ->
                              fun t3 ->
                                let uu____4622 =
                                  let uu____4623 =
                                    let uu____4624 =
                                      let uu____4625 =
                                        let uu____4626 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4626
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4625 in
                                    [uu____4624] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4623 in
                                uu____4622 FStar_Pervasives_Native.None
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
                       (lid, uu____4711, uu____4712, uu____4713, uu____4714,
                        uu____4715)
                       -> lid
                   | uu____4724 -> failwith "Impossible!") tcs in
            let uu____4725 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid, us, uu____4737, uu____4738, uu____4739, uu____4740)
                  -> (lid, us)
              | uu____4749 -> failwith "Impossible!" in
            match uu____4725 with
            | (lid, us) ->
                let uu____4758 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____4758 with
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
                         let uu____4785 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____4785 fml []
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
          let uu____4831 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___57_4856 ->
                    match uu___57_4856 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____4857;
                        FStar_Syntax_Syntax.sigrng = uu____4858;
                        FStar_Syntax_Syntax.sigquals = uu____4859;
                        FStar_Syntax_Syntax.sigmeta = uu____4860;
                        FStar_Syntax_Syntax.sigattrs = uu____4861;_} -> true
                    | uu____4882 -> false)) in
          match uu____4831 with
          | (tys, datas) ->
              ((let uu____4904 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___58_4913 ->
                          match uu___58_4913 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____4914;
                              FStar_Syntax_Syntax.sigrng = uu____4915;
                              FStar_Syntax_Syntax.sigquals = uu____4916;
                              FStar_Syntax_Syntax.sigmeta = uu____4917;
                              FStar_Syntax_Syntax.sigattrs = uu____4918;_} ->
                              false
                          | uu____4937 -> true)) in
                if uu____4904
                then
                  let uu____4938 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____4938
                else ());
               (let env0 = env in
                let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____4947 =
                       let uu____4948 = FStar_List.hd tys in
                       uu____4948.FStar_Syntax_Syntax.sigel in
                     match uu____4947 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____4951, uvs, uu____4953, uu____4954,
                          uu____4955, uu____4956)
                         -> uvs
                     | uu____4965 -> failwith "Impossible, can't happen!") in
                let uu____4968 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (tys, datas)
                  else
                    (let uu____4990 =
                       FStar_Syntax_Subst.univ_var_opening univs1 in
                     match uu____4990 with
                     | (subst1, univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid, uu____5026, bs, t, l1, l2) ->
                                      let uu____5039 =
                                        let uu____5056 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs in
                                        let uu____5057 =
                                          let uu____5058 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1 in
                                          FStar_Syntax_Subst.subst uu____5058
                                            t in
                                        (lid, univs2, uu____5056, uu____5057,
                                          l1, l2) in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____5039
                                  | uu____5071 ->
                                      failwith "Impossible, can't happen" in
                                let uu___65_5072 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___65_5072.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___65_5072.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___65_5072.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___65_5072.FStar_Syntax_Syntax.sigattrs)
                                }) tys in
                         let datas1 =
                           FStar_List.map
                             (fun se ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid, uu____5082, t, lid_t, x, l) ->
                                      let uu____5091 =
                                        let uu____5106 =
                                          FStar_Syntax_Subst.subst subst1 t in
                                        (lid, univs2, uu____5106, lid_t, x,
                                          l) in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____5091
                                  | uu____5111 ->
                                      failwith "Impossible, can't happen" in
                                let uu___66_5112 = se in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___66_5112.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___66_5112.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___66_5112.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___66_5112.FStar_Syntax_Syntax.sigattrs)
                                }) datas in
                         (tys1, datas1)) in
                match uu____4968 with
                | (tys1, datas1) ->
                    let uu____5137 =
                      FStar_List.fold_right
                        (fun tc ->
                           fun uu____5176 ->
                             match uu____5176 with
                             | (env1, all_tcs, g) ->
                                 let uu____5216 = tc_tycon env1 tc in
                                 (match uu____5216 with
                                  | (env2, tc1, tc_u, guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u in
                                      ((let uu____5243 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Low in
                                        if uu____5243
                                        then
                                          let uu____5244 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1 in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____5244
                                        else ());
                                       (let uu____5246 =
                                          let uu____5247 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g' in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____5247 in
                                        (env2, ((tc1, tc_u) :: all_tcs),
                                          uu____5246))))) tys1
                        (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                    (match uu____5137 with
                     | (env1, tcs, g) ->
                         let uu____5293 =
                           FStar_List.fold_right
                             (fun se ->
                                fun uu____5315 ->
                                  match uu____5315 with
                                  | (datas2, g1) ->
                                      let uu____5334 =
                                        let uu____5339 = tc_data env1 tcs in
                                        uu____5339 se in
                                      (match uu____5334 with
                                       | (data, g') ->
                                           let uu____5354 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g' in
                                           ((data :: datas2), uu____5354)))
                             datas1 ([], g) in
                         (match uu____5293 with
                          | (datas2, g1) ->
                              let uu____5375 =
                                generalize_and_inst_within env0 g1 tcs datas2 in
                              (match uu____5375 with
                               | (tcs1, datas3) ->
                                   let sig_bndle =
                                     let uu____5405 =
                                       FStar_TypeChecker_Env.get_range env0 in
                                     let uu____5406 =
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
                                         uu____5405;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____5406
                                     } in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l, univs2, binders, typ,
                                                 uu____5432, uu____5433)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____5449 =
                                                    let uu____5454 =
                                                      let uu____5455 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected in
                                                      let uu____5456 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____5455 uu____5456 in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____5454) in
                                                  FStar_Errors.raise_error
                                                    uu____5449
                                                    se.FStar_Syntax_Syntax.sigrng in
                                                let uu____5457 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l in
                                                (match uu____5457 with
                                                 | FStar_Pervasives_Native.None
                                                     -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,
                                                      uu____5473)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____5494 ->
                                                             let uu____5495 =
                                                               let uu____5498
                                                                 =
                                                                 let uu____5499
                                                                   =
                                                                   let uu____5512
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ in
                                                                   (binders,
                                                                    uu____5512) in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____5499 in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____5498 in
                                                             uu____5495
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
                                                       let uu____5518 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ in
                                                       (match uu____5518 with
                                                        | (uu____5523,
                                                           inferred) ->
                                                            let uu____5525 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1 in
                                                            (match uu____5525
                                                             with
                                                             | (uu____5530,
                                                                expected) ->
                                                                 let uu____5532
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected in
                                                                 if
                                                                   uu____5532
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____5535 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))