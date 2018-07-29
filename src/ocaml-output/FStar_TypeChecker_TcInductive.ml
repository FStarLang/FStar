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
      (FStar_TypeChecker_Env.env_t,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let env0 = env  in
          let uu____74 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____74 with
           | (usubst,uvs1) ->
               let uu____101 =
                 let uu____108 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____109 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____110 =
                   let uu____111 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____111 k  in
                 (uu____108, uu____109, uu____110)  in
               (match uu____101 with
                | (env1,tps1,k1) ->
                    let uu____131 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____131 with
                     | (tps2,k2) ->
                         let uu____166 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____166 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____207 =
                                FStar_Syntax_Util.arrow_formals k2  in
                              (match uu____207 with
                               | (indices,t) ->
                                   let uu____252 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____252 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____293 =
                                          let uu____300 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____300 with
                                          | (t1,uu____314,g) ->
                                              let uu____320 =
                                                let uu____321 =
                                                  let uu____322 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Env.conj_guard
                                                    guard_params uu____322
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____321
                                                 in
                                              (t1, uu____320)
                                           in
                                        (match uu____293 with
                                         | (t1,guard) ->
                                             let k3 =
                                               let uu____342 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____342
                                                in
                                             let uu____345 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____345 with
                                              | (t_type,u) ->
                                                  ((let uu____365 =
                                                      let uu____366 =
                                                        FStar_TypeChecker_Rel.subtype_nosmt_force
                                                          env1 t1 t_type
                                                         in
                                                      Prims.op_Negation
                                                        uu____366
                                                       in
                                                    if uu____365
                                                    then
                                                      let uu____367 =
                                                        let uu____372 =
                                                          let uu____373 =
                                                            FStar_Syntax_Print.term_to_string
                                                              t1
                                                             in
                                                          let uu____374 =
                                                            FStar_Ident.string_of_lid
                                                              tc
                                                             in
                                                          FStar_Util.format2
                                                            "Type annotation %s for inductive %s is not a subtype of Type"
                                                            uu____373
                                                            uu____374
                                                           in
                                                        (FStar_Errors.Error_InductiveAnnotNotAType,
                                                          uu____372)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____367
                                                        s.FStar_Syntax_Syntax.sigrng
                                                    else ());
                                                   (let usubst1 =
                                                      FStar_Syntax_Subst.univ_var_closing
                                                        uvs1
                                                       in
                                                    let guard1 =
                                                      FStar_TypeChecker_Util.close_guard_implicits
                                                        env1
                                                        (FStar_List.append
                                                           tps3 indices1)
                                                        guard
                                                       in
                                                    let t_tc =
                                                      let uu____389 =
                                                        let uu____398 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____415 =
                                                          let uu____424 =
                                                            let uu____437 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____437
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____424
                                                           in
                                                        FStar_List.append
                                                          uu____398 uu____415
                                                         in
                                                      let uu____460 =
                                                        let uu____463 =
                                                          let uu____464 =
                                                            let uu____469 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____469
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____464
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____463
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____389 uu____460
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k4 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k3
                                                       in
                                                    let uu____486 =
                                                      let uu____491 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____492 =
                                                        let uu____493 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____493 k4
                                                         in
                                                      (uu____491, uu____492)
                                                       in
                                                    match uu____486 with
                                                    | (tps5,k5) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____513 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____513,
                                                          (let uu___348_519 =
                                                             s  in
                                                           {
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                  (tc, uvs1,
                                                                    tps5, k5,
                                                                    mutuals,
                                                                    data));
                                                             FStar_Syntax_Syntax.sigrng
                                                               =
                                                               (uu___348_519.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___348_519.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___348_519.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___348_519.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard1)))))))))))
      | uu____524 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____592 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____592 with
             | (usubst,_uvs1) ->
                 let uu____615 =
                   let uu____620 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____621 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____620, uu____621)  in
                 (match uu____615 with
                  | (env1,t1) ->
                      let uu____628 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____675  ->
                               match uu____675 with
                               | (se1,u_tc) ->
                                   let uu____690 =
                                     let uu____691 =
                                       let uu____692 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____692  in
                                     FStar_Ident.lid_equals tc_lid uu____691
                                      in
                                   if uu____690
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____711,uu____712,tps,uu____714,uu____715,uu____716)
                                          ->
                                          let tps1 =
                                            let uu____750 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____750
                                              (FStar_List.map
                                                 (fun uu____790  ->
                                                    match uu____790 with
                                                    | (x,uu____804) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____812 =
                                            let uu____819 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____819, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____812
                                      | uu____826 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____899 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____899
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____628 with
                       | (env2,tps,u_tc) ->
                           let uu____966 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____982 =
                               let uu____983 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____983.FStar_Syntax_Syntax.n  in
                             match uu____982 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____1022 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____1022 with
                                  | (uu____1063,bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let subst1 =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i  ->
                                                fun uu____1134  ->
                                                  match uu____1134 with
                                                  | (x,uu____1142) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____1147 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____1147)
                             | uu____1148 -> ([], t2)  in
                           (match uu____966 with
                            | (arguments,result) ->
                                ((let uu____1192 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1192
                                  then
                                    let uu____1193 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1194 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1195 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1193 uu____1194 uu____1195
                                  else ());
                                 (let uu____1197 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1197 with
                                  | (arguments1,env',us) ->
                                      let uu____1231 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____1231 with
                                       | (result1,res_lcomp) ->
                                           let ty =
                                             let uu____1247 =
                                               unfold_whnf env2
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_All.pipe_right uu____1247
                                               FStar_Syntax_Util.unrefine
                                              in
                                           ((let uu____1249 =
                                               let uu____1250 =
                                                 FStar_Syntax_Subst.compress
                                                   ty
                                                  in
                                               uu____1250.FStar_Syntax_Syntax.n
                                                in
                                             match uu____1249 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____1253 -> ()
                                             | uu____1254 ->
                                                 let uu____1255 =
                                                   let uu____1260 =
                                                     let uu____1261 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____1262 =
                                                       FStar_Syntax_Print.term_to_string
                                                         ty
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____1261 uu____1262
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____1260)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1255
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____1263 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____1263 with
                                             | (head1,uu____1285) ->
                                                 let g_uvs =
                                                   let uu____1311 =
                                                     let uu____1312 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____1312.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1311 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____1316;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____1317;_},tuvs)
                                                       ->
                                                       if
                                                         (FStar_List.length
                                                            _uvs1)
                                                           =
                                                           (FStar_List.length
                                                              tuvs)
                                                       then
                                                         FStar_List.fold_left2
                                                           (fun g  ->
                                                              fun u1  ->
                                                                fun u2  ->
                                                                  let uu____1334
                                                                    =
                                                                    let uu____1335
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1336
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'
                                                                    uu____1335
                                                                    uu____1336
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1334)
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
                                                   | uu____1339 ->
                                                       let uu____1340 =
                                                         let uu____1345 =
                                                           let uu____1346 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____1347 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____1346
                                                             uu____1347
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____1345)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1340
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____1362  ->
                                                          fun u_x  ->
                                                            match uu____1362
                                                            with
                                                            | (x,uu____1371)
                                                                ->
                                                                let uu____1376
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____1376)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1380 =
                                                     let uu____1389 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1429 
                                                               ->
                                                               match uu____1429
                                                               with
                                                               | (x,uu____1443)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1389 arguments1
                                                      in
                                                   let uu____1456 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1380 uu____1456
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___349_1461 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___349_1461.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___349_1461.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___349_1461.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___349_1461.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1464 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs  in
          let g1 =
            let uu___350_1529 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___350_1529.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___350_1529.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___350_1529.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1539 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1539
           then
             let uu____1540 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1540
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1580  ->
                     match uu____1580 with
                     | (se,uu____1586) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1587,uu____1588,tps,k,uu____1591,uu____1592)
                              ->
                              let uu____1625 =
                                let uu____1626 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1626
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1625
                          | uu____1631 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1659,uu____1660,t,uu____1662,uu____1663,uu____1664)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1677 -> failwith "Impossible"))
              in
           let t =
             let uu____1681 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1681
              in
           (let uu____1691 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1691
            then
              let uu____1692 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1692
            else ());
           (let uu____1694 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1694 with
            | (uvs,t1) ->
                ((let uu____1714 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1714
                  then
                    let uu____1715 =
                      let uu____1716 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1716
                        (FStar_String.concat ", ")
                       in
                    let uu____1727 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1715 uu____1727
                  else ());
                 (let uu____1729 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1729 with
                  | (uvs1,t2) ->
                      let uu____1752 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1752 with
                       | (args,uu____1776) ->
                           let uu____1797 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1797 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1902  ->
                                       fun uu____1903  ->
                                         match (uu____1902, uu____1903) with
                                         | ((x,uu____1925),(se,uu____1927))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1943,tps,uu____1945,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1981 =
                                                    let uu____1986 =
                                                      let uu____1987 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1987.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1986 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____2016 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____2016
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____2094
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____2113 -> ([], ty)
                                                     in
                                                  (match uu____1981 with
                                                   | (tps1,t3) ->
                                                       let uu___351_2122 = se
                                                          in
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
                                                           (uu___351_2122.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___351_2122.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___351_2122.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___351_2122.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____2127 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____2133 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_16  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_16))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___339_2157  ->
                                                match uu___339_2157 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____2163,uu____2164,uu____2165,uu____2166,uu____2167);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____2168;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____2169;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____2170;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____2171;_}
                                                    -> (tc, uvs_universes)
                                                | uu____2208 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____2231  ->
                                           fun d  ->
                                             match uu____2231 with
                                             | (t3,uu____2240) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____2246,uu____2247,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____2264 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2264
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___352_2265 = d
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___352_2265.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___352_2265.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___352_2265.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___352_2265.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____2268 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____2283 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2283
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2295 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2295
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2311 =
      let uu____2312 = FStar_Syntax_Subst.compress t  in
      uu____2312.FStar_Syntax_Syntax.n  in
    match uu____2311 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2335 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2340 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____2393 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2462  ->
               match uu____2462 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2505 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2505  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2393
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2749 =
             let uu____2750 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2750
              in
           debug_log env uu____2749);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype
              in
           (let uu____2753 =
              let uu____2754 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2754
               in
            debug_log env uu____2753);
           (let uu____2757 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2757) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2768 =
                  let uu____2769 = FStar_Syntax_Subst.compress btype1  in
                  uu____2769.FStar_Syntax_Syntax.n  in
                match uu____2768 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2798 = try_get_fv t  in
                    (match uu____2798 with
                     | (fv,us) ->
                         let uu____2809 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2809
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2821  ->
                                 match uu____2821 with
                                 | (t1,uu____2829) ->
                                     let uu____2834 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2834) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let check_comp1 =
                        let c1 =
                          let uu____2884 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2884
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2888 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2888
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2908  ->
                               match uu____2908 with
                               | (b,uu____2916) ->
                                   let uu____2921 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2921) sbs)
                           &&
                           ((let uu____2926 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2926 with
                             | (uu____2931,return_type) ->
                                 let uu____2953 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2953)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2974 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2976 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2979) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____3010) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____3036,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____3094  ->
                          match uu____3094 with
                          | (p,uu____3106,t) ->
                              let bs =
                                let uu____3125 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____3125
                                 in
                              let uu____3134 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____3134 with
                               | (bs1,t1) ->
                                   let uu____3161 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____3161)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3183,uu____3184)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3246 ->
                    ((let uu____3248 =
                        let uu____3249 =
                          let uu____3250 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____3251 =
                            let uu____3252 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____3252  in
                          Prims.strcat uu____3250 uu____3251  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____3249
                         in
                      debug_log env uu____3248);
                     false)))))

and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              (let uu____3270 =
                 let uu____3271 =
                   let uu____3272 =
                     let uu____3273 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____3273  in
                   Prims.strcat ilid.FStar_Ident.str uu____3272  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____3271
                  in
               debug_log env uu____3270);
              (let uu____3274 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3274 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3287 =
                       FStar_TypeChecker_Env.lookup_attrs_of_lid env ilid  in
                     (match uu____3287 with
                      | FStar_Pervasives_Native.None  ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some [] ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some attrs ->
                          let uu____3313 =
                            FStar_All.pipe_right attrs
                              (FStar_Util.for_some
                                 (fun tm  ->
                                    let uu____3320 =
                                      let uu____3321 =
                                        FStar_Syntax_Subst.compress tm  in
                                      uu____3321.FStar_Syntax_Syntax.n  in
                                    match uu____3320 with
                                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.assume_strictly_positive_attr_lid
                                    | uu____3325 -> false))
                             in
                          if uu____3313
                          then
                            ((let uu____3327 =
                                let uu____3328 =
                                  FStar_Ident.string_of_lid ilid  in
                                FStar_Util.format1
                                  "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                  uu____3328
                                 in
                              debug_log env uu____3327);
                             true)
                          else
                            (debug_log env
                               "Checking nested positivity, not an inductive, return false";
                             false))
                   else
                     (let uu____3332 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3332
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____3356 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3356  in
                         (let uu____3360 =
                            let uu____3361 =
                              let uu____3362 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____3362
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____3361
                             in
                          debug_log env uu____3360);
                         (let uu____3364 =
                            let uu____3365 = FStar_ST.op_Bang unfolded  in
                            let uu____3411 =
                              let uu____3418 =
                                let uu____3423 =
                                  let uu____3424 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3424  in
                                (ilid, uu____3423)  in
                              [uu____3418]  in
                            FStar_List.append uu____3365 uu____3411  in
                          FStar_ST.op_Colon_Equals unfolded uu____3364);
                         FStar_List.for_all
                           (fun d  ->
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
  fun ty_lid  ->
    fun dlid  ->
      fun ilid  ->
        fun us  ->
          fun args  ->
            fun num_ibs  ->
              fun unfolded  ->
                fun env  ->
                  debug_log env
                    (Prims.strcat
                       "Checking nested positivity in data constructor "
                       (Prims.strcat dlid.FStar_Ident.str
                          (Prims.strcat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____3569 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3569 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3599 ->
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
                             dt
                            in
                         (let uu____3602 =
                            let uu____3603 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3603
                             in
                          debug_log env uu____3602);
                         (let uu____3604 =
                            let uu____3605 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3605.FStar_Syntax_Syntax.n  in
                          match uu____3604 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3631 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3631 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3694 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3694 dbs1
                                       in
                                    let c1 =
                                      let uu____3698 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3698 c
                                       in
                                    let uu____3701 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3701 with
                                     | (args1,uu____3735) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((FStar_Pervasives_Native.fst
                                                             ib),
                                                           (FStar_Pervasives_Native.fst
                                                              arg))]) [] ibs1
                                             args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____3827 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3827 c1
                                            in
                                         ((let uu____3837 =
                                             let uu____3838 =
                                               let uu____3839 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3840 =
                                                 let uu____3841 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3841
                                                  in
                                               Prims.strcat uu____3839
                                                 uu____3840
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3838
                                              in
                                           debug_log env uu____3837);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3872 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3874 =
                                  let uu____3875 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3875.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3874
                                  ilid num_ibs unfolded env))))))

and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun t  ->
      fun ilid  ->
        fun num_ibs  ->
          fun unfolded  ->
            fun env  ->
              match t with
              | FStar_Syntax_Syntax.Tm_app (t1,args) ->
                  (debug_log env
                     "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself";
                   (let uu____3941 = try_get_fv t1  in
                    match uu____3941 with
                    | (fv,uu____3947) ->
                        let uu____3952 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3952
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3977 =
                      let uu____3978 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3978
                       in
                    debug_log env uu____3977);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3980 =
                      FStar_List.fold_left
                        (fun uu____3999  ->
                           fun b  ->
                             match uu____3999 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____4022 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____4045 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____4022, uu____4045))) (true, env)
                        sbs1
                       in
                    match uu____3980 with | (b,uu____4059) -> b))
              | uu____4060 ->
                  failwith "Nested positive check, unhandled case"

let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____4111 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____4111 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____4141 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____4143 =
                      let uu____4144 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____4144
                       in
                    debug_log env uu____4143);
                   (let uu____4145 =
                      let uu____4146 = FStar_Syntax_Subst.compress dt  in
                      uu____4146.FStar_Syntax_Syntax.n  in
                    match uu____4145 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____4149 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4152) ->
                        let dbs1 =
                          let uu____4182 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____4182  in
                        let dbs2 =
                          let uu____4232 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____4232 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____4237 =
                            let uu____4238 =
                              let uu____4239 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____4239 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____4238
                             in
                          debug_log env uu____4237);
                         (let uu____4246 =
                            FStar_List.fold_left
                              (fun uu____4265  ->
                                 fun b  ->
                                   match uu____4265 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____4288 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____4311 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____4288, uu____4311)))
                              (true, env) dbs3
                             in
                          match uu____4246 with | (b,uu____4325) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____4326,uu____4327) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4384 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4402 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4418,uu____4419,uu____4420) -> (lid, us, bs)
        | uu____4453 -> failwith "Impossible!"  in
      match uu____4402 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4463 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4463 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4486 =
                 let uu____4489 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4489  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4501 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4501
                      unfolded_inductives env2) uu____4486)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4531,uu____4532,t,uu____4534,uu____4535,uu____4536) -> t
    | uu____4549 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4569 =
         let uu____4570 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4570 haseq_suffix  in
       uu____4569 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4590 =
      let uu____4593 =
        let uu____4596 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4596]  in
      FStar_List.append lid.FStar_Ident.ns uu____4593  in
    FStar_Ident.lid_of_ids uu____4590
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple5)
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____4641 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4655,bs,t,uu____4658,uu____4659) -> (lid, bs, t)
            | uu____4692 -> failwith "Impossible!"  in
          match uu____4641 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4714 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4714 t  in
              let uu____4723 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4723 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4761 =
                       let uu____4762 = FStar_Syntax_Subst.compress t2  in
                       uu____4762.FStar_Syntax_Syntax.n  in
                     match uu____4761 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4766) -> ibs
                     | uu____4787 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4796 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4797 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4796 uu____4797
                      in
                   let ind1 =
                     let uu____4803 =
                       let uu____4808 =
                         FStar_List.map
                           (fun uu____4825  ->
                              match uu____4825 with
                              | (bv,aq) ->
                                  let uu____4844 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4844, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4808  in
                     uu____4803 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4852 =
                       let uu____4857 =
                         FStar_List.map
                           (fun uu____4874  ->
                              match uu____4874 with
                              | (bv,aq) ->
                                  let uu____4893 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4893, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4857  in
                     uu____4852 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4901 =
                       let uu____4906 =
                         let uu____4907 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4907]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4906
                        in
                     uu____4901 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4958 =
                            let uu____4959 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4959  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4958) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4972 =
                              let uu____4975 =
                                let uu____4980 =
                                  let uu____4981 =
                                    let uu____4990 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4990  in
                                  [uu____4981]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4980
                                 in
                              uu____4975 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4972)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___353_5015 = fml  in
                     let uu____5016 =
                       let uu____5017 =
                         let uu____5024 =
                           let uu____5025 =
                             let uu____5038 =
                               let uu____5049 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____5049]  in
                             [uu____5038]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____5025  in
                         (fml, uu____5024)  in
                       FStar_Syntax_Syntax.Tm_meta uu____5017  in
                     {
                       FStar_Syntax_Syntax.n = uu____5016;
                       FStar_Syntax_Syntax.pos =
                         (uu___353_5015.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___353_5015.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____5104 =
                              let uu____5109 =
                                let uu____5110 =
                                  let uu____5119 =
                                    let uu____5120 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____5120 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____5119  in
                                [uu____5110]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____5109
                               in
                            uu____5104 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____5177 =
                              let uu____5182 =
                                let uu____5183 =
                                  let uu____5192 =
                                    let uu____5193 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____5193 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____5192  in
                                [uu____5183]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____5182
                               in
                            uu____5177 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____5269 =
            let uu____5270 = FStar_Syntax_Subst.compress dt1  in
            uu____5270.FStar_Syntax_Syntax.n  in
          match uu____5269 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5274) ->
              let dbs1 =
                let uu____5304 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____5304  in
              let dbs2 =
                let uu____5354 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____5354 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____5369 =
                           let uu____5374 =
                             let uu____5375 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____5375]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5374
                            in
                         uu____5369 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____5408 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____5408 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____5416 =
                       let uu____5421 =
                         let uu____5422 =
                           let uu____5431 =
                             let uu____5432 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____5432
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____5431  in
                         [uu____5422]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____5421
                        in
                     uu____5416 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5481 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term'
                               FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple4 ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident,FStar_Syntax_Syntax.term'
                                   FStar_Syntax_Syntax.syntax)
               FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple4)
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____5577,uu____5578,uu____5579,uu____5580,uu____5581)
                  -> lid
              | uu____5614 -> failwith "Impossible!"  in
            let uu____5615 = acc  in
            match uu____5615 with
            | (uu____5656,en,uu____5658,uu____5659) ->
                let uu____5684 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5684 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5763 = acc  in
                     (match uu____5763 with
                      | (l_axioms,env,guard',cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs  in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs  in
                          let t_datas =
                            FStar_List.filter
                              (fun s  ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____5845,uu____5846,uu____5847,t_lid,uu____5849,uu____5850)
                                     -> t_lid = lid
                                 | uu____5863 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5876 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5876)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5879 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5882 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5879, uu____5882)))
  
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let us =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5951,us,uu____5953,uu____5954,uu____5955,uu____5956)
                -> us
            | uu____5989 -> failwith "Impossible!"  in
          let uu____5990 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____5990 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____6015 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____6015 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____6105 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____6105 with
                     | (phi1,uu____6113) ->
                         ((let uu____6119 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____6119
                           then
                             let uu____6120 =
                               FStar_TypeChecker_Env.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____6120
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____6137  ->
                                    match uu____6137 with
                                    | (lid,fml) ->
                                        let fml1 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            us1 fml
                                           in
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
                                           }]) [] axioms
                              in
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
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____6205 =
                  let uu____6206 = FStar_Syntax_Subst.compress t  in
                  uu____6206.FStar_Syntax_Syntax.n  in
                match uu____6205 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____6213) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____6254 = is_mutual t'  in
                    if uu____6254
                    then true
                    else
                      (let uu____6256 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____6256)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____6276) -> is_mutual t'
                | uu____6281 -> false
              
              and exists_mutual uu___340_6282 =
                match uu___340_6282 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____6301 =
                let uu____6302 = FStar_Syntax_Subst.compress dt1  in
                uu____6302.FStar_Syntax_Syntax.n  in
              match uu____6301 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____6308) ->
                  let dbs1 =
                    let uu____6338 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____6338  in
                  let dbs2 =
                    let uu____6388 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____6388 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____6408 =
                               let uu____6413 =
                                 let uu____6414 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____6414]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____6413
                                in
                             uu____6408 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____6446 = is_mutual sort  in
                             if uu____6446
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort  in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3
                     in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____6458 =
                             let uu____6463 =
                               let uu____6464 =
                                 let uu____6473 =
                                   let uu____6474 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____6474 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____6473  in
                               [uu____6464]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____6463
                              in
                           uu____6458 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6523 -> acc
  
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle  ->
    fun mutuals  ->
      fun usubst  ->
        fun us  ->
          fun acc  ->
            fun ty  ->
              let uu____6572 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6594,bs,t,uu____6597,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6633 -> failwith "Impossible!"  in
              match uu____6572 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6656 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6656 t  in
                  let uu____6665 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6665 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6695 =
                           let uu____6696 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6696.FStar_Syntax_Syntax.n  in
                         match uu____6695 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6700) ->
                             ibs
                         | uu____6721 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6730 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6731 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6730
                           uu____6731
                          in
                       let ind1 =
                         let uu____6737 =
                           let uu____6742 =
                             FStar_List.map
                               (fun uu____6759  ->
                                  match uu____6759 with
                                  | (bv,aq) ->
                                      let uu____6778 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6778, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6742  in
                         uu____6737 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6786 =
                           let uu____6791 =
                             FStar_List.map
                               (fun uu____6808  ->
                                  match uu____6808 with
                                  | (bv,aq) ->
                                      let uu____6827 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6827, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6791  in
                         uu____6786 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6835 =
                           let uu____6840 =
                             let uu____6841 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6841]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6840
                            in
                         uu____6835 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6879,uu____6880,uu____6881,t_lid,uu____6883,uu____6884)
                                  -> t_lid = lid
                              | uu____6897 -> failwith "Impossible")
                           all_datas_in_the_bundle
                          in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas
                          in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind
                          in
                       let fml1 =
                         let uu___354_6907 = fml  in
                         let uu____6908 =
                           let uu____6909 =
                             let uu____6916 =
                               let uu____6917 =
                                 let uu____6930 =
                                   let uu____6941 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____6941]  in
                                 [uu____6930]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6917
                                in
                             (fml, uu____6916)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6909  in
                         {
                           FStar_Syntax_Syntax.n = uu____6908;
                           FStar_Syntax_Syntax.pos =
                             (uu___354_6907.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___354_6907.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6996 =
                                  let uu____7001 =
                                    let uu____7002 =
                                      let uu____7011 =
                                        let uu____7012 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____7012
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____7011
                                       in
                                    [uu____7002]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____7001
                                   in
                                uu____6996 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____7069 =
                                  let uu____7074 =
                                    let uu____7075 =
                                      let uu____7084 =
                                        let uu____7085 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____7085
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____7084
                                       in
                                    [uu____7075]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____7074
                                   in
                                uu____7069 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2
                          in
                       FStar_Syntax_Util.mk_conj acc fml3)
  
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let mutuals =
            FStar_List.map
              (fun ty  ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____7178,uu____7179,uu____7180,uu____7181,uu____7182)
                     -> lid
                 | uu____7215 -> failwith "Impossible!") tcs
             in
          let uu____7216 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____7228,uu____7229,uu____7230,uu____7231) ->
                (lid, us)
            | uu____7264 -> failwith "Impossible!"  in
          match uu____7216 with
          | (lid,us) ->
              let uu____7273 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____7273 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____7300 =
                       let uu____7301 =
                         let uu____7308 = get_haseq_axiom_lid lid  in
                         (uu____7308, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____7301  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____7300;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = []
                     }  in
                   [se])
  
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____7361 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___341_7386  ->
                    match uu___341_7386 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____7387;
                        FStar_Syntax_Syntax.sigrng = uu____7388;
                        FStar_Syntax_Syntax.sigquals = uu____7389;
                        FStar_Syntax_Syntax.sigmeta = uu____7390;
                        FStar_Syntax_Syntax.sigattrs = uu____7391;_} -> true
                    | uu____7412 -> false))
             in
          match uu____7361 with
          | (tys,datas) ->
              ((let uu____7434 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___342_7443  ->
                          match uu___342_7443 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____7444;
                              FStar_Syntax_Syntax.sigrng = uu____7445;
                              FStar_Syntax_Syntax.sigquals = uu____7446;
                              FStar_Syntax_Syntax.sigmeta = uu____7447;
                              FStar_Syntax_Syntax.sigattrs = uu____7448;_} ->
                              false
                          | uu____7467 -> true))
                   in
                if uu____7434
                then
                  let uu____7468 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____7468
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____7476 =
                       let uu____7477 = FStar_List.hd tys  in
                       uu____7477.FStar_Syntax_Syntax.sigel  in
                     match uu____7476 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____7480,uvs,uu____7482,uu____7483,uu____7484,uu____7485)
                         -> uvs
                     | uu____7518 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____7522 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____7548 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____7548 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____7586,bs,t,l1,l2) ->
                                      let uu____7623 =
                                        let uu____7640 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____7641 =
                                          let uu____7642 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____7642
                                            t
                                           in
                                        (lid, univs2, uu____7640, uu____7641,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____7623
                                  | uu____7655 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___355_7656 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___355_7656.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___355_7656.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___355_7656.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___355_7656.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____7666,t,lid_t,x,l) ->
                                      let uu____7683 =
                                        let uu____7698 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____7698, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____7683
                                  | uu____7701 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___356_7702 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___356_7702.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___356_7702.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___356_7702.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___356_7702.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____7703 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____7703, tys1, datas1))
                   in
                match uu____7522 with
                | (env1,tys1,datas1) ->
                    let uu____7729 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____7768  ->
                             match uu____7768 with
                             | (env2,all_tcs,g) ->
                                 let uu____7808 = tc_tycon env2 tc  in
                                 (match uu____7808 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7835 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7835
                                        then
                                          let uu____7836 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7836
                                        else ());
                                       (let uu____7838 =
                                          let uu____7839 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7839
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7838))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____7729 with
                     | (env2,tcs,g) ->
                         let uu____7885 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7907  ->
                                  match uu____7907 with
                                  | (datas2,g1) ->
                                      let uu____7926 =
                                        let uu____7931 = tc_data env2 tcs  in
                                        uu____7931 se  in
                                      (match uu____7926 with
                                       | (data,g') ->
                                           let uu____7948 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7948)))
                             datas1 ([], g)
                            in
                         (match uu____7885 with
                          | (datas2,g1) ->
                              let uu____7969 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7987 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7987, datas2))
                                 in
                              (match uu____7969 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____8019 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____8020 =
                                       FStar_List.collect
                                         (fun s  ->
                                            s.FStar_Syntax_Syntax.sigattrs)
                                         ses
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_bundle
                                            ((FStar_List.append tcs1 datas3),
                                              lids));
                                       FStar_Syntax_Syntax.sigrng =
                                         uu____8019;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____8020
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____8046,uu____8047)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____8091 =
                                                    let uu____8096 =
                                                      let uu____8097 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____8098 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____8097 uu____8098
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____8096)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____8091
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____8099 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____8099 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____8123)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____8178 ->
                                                             let uu____8187 =
                                                               let uu____8194
                                                                 =
                                                                 let uu____8195
                                                                   =
                                                                   let uu____8210
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____8210)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____8195
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____8194
                                                                in
                                                             uu____8187
                                                               FStar_Pervasives_Native.None
                                                               se.FStar_Syntax_Syntax.sigrng
                                                          in
                                                       (univs2, body)  in
                                                     if
                                                       (FStar_List.length
                                                          univs2)
                                                         =
                                                         (FStar_List.length
                                                            (FStar_Pervasives_Native.fst
                                                               expected_typ1))
                                                     then
                                                       let uu____8234 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____8234 with
                                                        | (uu____8239,inferred)
                                                            ->
                                                            let uu____8249 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____8249
                                                             with
                                                             | (uu____8254,expected)
                                                                 ->
                                                                 let uu____8264
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____8264
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____8267 -> ()));
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
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____8359 =
                            let uu____8366 =
                              let uu____8367 =
                                let uu____8374 =
                                  let uu____8377 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____8377  in
                                (uu____8374, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____8367  in
                            FStar_Syntax_Syntax.mk uu____8366  in
                          uu____8359 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____8414  ->
                                  match uu____8414 with
                                  | (x,imp) ->
                                      let uu____8433 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____8433, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____8437 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____8437  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               let uu____8458 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____8458
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____8459 =
                               let uu____8462 =
                                 let uu____8465 =
                                   let uu____8470 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____8471 =
                                     let uu____8472 =
                                       let uu____8481 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____8481
                                        in
                                     [uu____8472]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____8470
                                     uu____8471
                                    in
                                 uu____8465 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____8462  in
                             FStar_Syntax_Util.refine x uu____8459  in
                           let uu____8508 =
                             let uu___357_8509 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___357_8509.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___357_8509.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____8508)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____8526 =
                          FStar_List.map
                            (fun uu____8550  ->
                               match uu____8550 with
                               | (x,uu____8564) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____8526 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____8623  ->
                                match uu____8623 with
                                | (x,uu____8637) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____8647 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____8647)
                          &&
                          (((tc.FStar_Ident.ident).FStar_Ident.idText =
                              "dtuple2")
                             ||
                             (FStar_List.existsb
                                (fun s  ->
                                   s =
                                     (tc.FStar_Ident.ident).FStar_Ident.idText)
                                early_prims_inductives))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             early_prims_inductive ||
                               (let uu____8660 =
                                  let uu____8661 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____8661.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____8660)
                              in
                           let quals =
                             let uu____8665 =
                               FStar_List.filter
                                 (fun uu___343_8669  ->
                                    match uu___343_8669 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____8670 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____8665
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____8705 =
                                 let uu____8706 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____8706  in
                               FStar_Syntax_Syntax.mk_Total uu____8705  in
                             let uu____8707 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____8707
                              in
                           let decl =
                             let uu____8711 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____8711;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____8713 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____8713
                            then
                              let uu____8714 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____8714
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
                                          (fun j  ->
                                             fun uu____8765  ->
                                               match uu____8765 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____8789 =
                                                       let uu____8792 =
                                                         let uu____8793 =
                                                           let uu____8800 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____8800,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8793
                                                          in
                                                       pos uu____8792  in
                                                     (uu____8789, b)
                                                   else
                                                     (let uu____8806 =
                                                        let uu____8809 =
                                                          let uu____8810 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8810
                                                           in
                                                        pos uu____8809  in
                                                      (uu____8806, b))))
                                      in
                                   let pat_true =
                                     let uu____8828 =
                                       let uu____8831 =
                                         let uu____8832 =
                                           let uu____8845 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____8845, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8832
                                          in
                                       pos uu____8831  in
                                     (uu____8828,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____8879 =
                                       let uu____8882 =
                                         let uu____8883 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8883
                                          in
                                       pos uu____8882  in
                                     (uu____8879,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8897 =
                                     let uu____8904 =
                                       let uu____8905 =
                                         let uu____8928 =
                                           let uu____8945 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8960 =
                                             let uu____8977 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8977]  in
                                           uu____8945 :: uu____8960  in
                                         (arg_exp, uu____8928)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8905
                                        in
                                     FStar_Syntax_Syntax.mk uu____8904  in
                                   uu____8897 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____9056 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____9056
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                       (Prims.parse_int "1"))
                                else
                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")
                                 in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____9070 =
                                  let uu____9075 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____9075  in
                                let uu____9076 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____9070
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____9076 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____9082 =
                                  let uu____9083 =
                                    let uu____9090 =
                                      let uu____9093 =
                                        let uu____9094 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____9094
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____9093]  in
                                    ((false, [lb]), uu____9090)  in
                                  FStar_Syntax_Syntax.Sig_let uu____9083  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____9082;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____9106 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____9106
                               then
                                 let uu____9107 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____9107
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9177  ->
                                  match uu____9177 with
                                  | (a,uu____9185) ->
                                      let uu____9190 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____9190 with
                                       | (field_name,uu____9196) ->
                                           let field_proj_tm =
                                             let uu____9198 =
                                               let uu____9199 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____9199
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____9198 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____9224 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____9266  ->
                                    match uu____9266 with
                                    | (x,uu____9276) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____9282 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____9282 with
                                         | (field_name,uu____9290) ->
                                             let t =
                                               let uu____9294 =
                                                 let uu____9295 =
                                                   let uu____9298 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____9298
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____9295
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____9294
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____9303 =
                                                    let uu____9304 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____9304.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____9303)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____9320 =
                                                   FStar_List.filter
                                                     (fun uu___344_9324  ->
                                                        match uu___344_9324
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____9325 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____9320
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___345_9338  ->
                                                         match uu___345_9338
                                                         with
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____9339 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
                                             let decl =
                                               let uu____9347 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____9347;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____9349 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____9349
                                               then
                                                 let uu____9350 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____9350
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____9396  ->
                                                             match uu____9396
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____9420
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____9420,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____9436
                                                                    =
                                                                    let uu____9439
                                                                    =
                                                                    let uu____9440
                                                                    =
                                                                    let uu____9447
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____9447,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____9440
                                                                     in
                                                                    pos
                                                                    uu____9439
                                                                     in
                                                                    (uu____9436,
                                                                    b))
                                                                   else
                                                                    (let uu____9453
                                                                    =
                                                                    let uu____9456
                                                                    =
                                                                    let uu____9457
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____9457
                                                                     in
                                                                    pos
                                                                    uu____9456
                                                                     in
                                                                    (uu____9453,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____9475 =
                                                     let uu____9478 =
                                                       let uu____9479 =
                                                         let uu____9492 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____9492,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____9479
                                                        in
                                                     pos uu____9478  in
                                                   let uu____9501 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____9475,
                                                     FStar_Pervasives_Native.None,
                                                     uu____9501)
                                                    in
                                                 let body =
                                                   let uu____9517 =
                                                     let uu____9524 =
                                                       let uu____9525 =
                                                         let uu____9548 =
                                                           let uu____9565 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____9565]  in
                                                         (arg_exp,
                                                           uu____9548)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____9525
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____9524
                                                      in
                                                   uu____9517
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____9633 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____9633
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       (FStar_Syntax_Syntax.Delta_equational_at_level
                                                          (Prims.parse_int "1"))
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational_at_level
                                                       (Prims.parse_int "1")
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____9644 =
                                                     let uu____9649 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____9649
                                                      in
                                                   let uu____9650 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____9644;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____9650;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____9656 =
                                                     let uu____9657 =
                                                       let uu____9664 =
                                                         let uu____9667 =
                                                           let uu____9668 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____9668
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____9667]  in
                                                       ((false, [lb]),
                                                         uu____9664)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____9657
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____9656;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____9680 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____9680
                                                  then
                                                    let uu____9681 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____9681
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____9224 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9729) when
              let uu____9742 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9742 ->
              let uu____9743 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9743 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9765 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9765 with
                    | (formals,uu____9783) ->
                        let uu____9804 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9866 =
                                   let uu____9867 =
                                     let uu____9868 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9868  in
                                   FStar_Ident.lid_equals typ_lid uu____9867
                                    in
                                 if uu____9866
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9907,uvs',tps,typ0,uu____9911,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9972 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____10073 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____10073
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9804 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____10150 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____10150 with
                              | (indices,uu____10168) ->
                                  let refine_domain =
                                    let uu____10190 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___346_10195  ->
                                              match uu___346_10195 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____10196 -> true
                                              | uu____10205 -> false))
                                       in
                                    if uu____10190
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___347_10215 =
                                      match uu___347_10215 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____10218,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____10230 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____10231 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____10231 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
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
                                    else iquals  in
                                  let fields =
                                    let uu____10242 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____10242 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____10325  ->
                                               fun uu____10326  ->
                                                 match (uu____10325,
                                                         uu____10326)
                                                 with
                                                 | ((x,uu____10352),(x',uu____10354))
                                                     ->
                                                     let uu____10375 =
                                                       let uu____10382 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____10382)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____10375) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____10387 -> []
  