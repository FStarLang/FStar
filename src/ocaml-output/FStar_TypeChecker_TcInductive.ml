open Prims
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
          let uu____42 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____42 with
           | (usubst,uvs1) ->
               let uu____69 =
                 let uu____76 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____77 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____78 =
                   let uu____79 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____79 k  in
                 (uu____76, uu____77, uu____78)  in
               (match uu____69 with
                | (env1,tps1,k1) ->
                    let uu____97 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____97 with
                     | (tps2,k2) ->
                         let uu____112 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____112 with
                          | (tps3,env_tps,guard_params,us) ->
                              let k3 =
                                FStar_TypeChecker_Normalize.unfold_whnf env1
                                  k2
                                 in
                              let uu____134 =
                                FStar_Syntax_Util.arrow_formals k3  in
                              (match uu____134 with
                               | (indices,t) ->
                                   let uu____173 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____173 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____194 =
                                          let uu____199 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____199 with
                                          | (t1,uu____211,g) ->
                                              let uu____213 =
                                                let uu____214 =
                                                  let uu____215 =
                                                    FStar_TypeChecker_Rel.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    guard_params uu____215
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____214
                                                 in
                                              (t1, uu____213)
                                           in
                                        (match uu____194 with
                                         | (t1,guard) ->
                                             let k4 =
                                               let uu____229 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____229
                                                in
                                             let uu____232 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____232 with
                                              | (t_type,u) ->
                                                  ((let uu____248 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env' t1 t_type
                                                       in
                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                      env' uu____248);
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
                                                      let uu____260 =
                                                        let uu____267 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____280 =
                                                          let uu____287 =
                                                            let uu____298 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____298
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____287
                                                           in
                                                        FStar_List.append
                                                          uu____267 uu____280
                                                         in
                                                      let uu____315 =
                                                        let uu____318 =
                                                          let uu____319 =
                                                            let uu____324 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____324
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____319
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____318
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____260 uu____315
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k5 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k4
                                                       in
                                                    let uu____337 =
                                                      let uu____342 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____343 =
                                                        let uu____344 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____344 k5
                                                         in
                                                      (uu____342, uu____343)
                                                       in
                                                    match uu____337 with
                                                    | (tps5,k6) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____362 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____362,
                                                          (let uu___149_368 =
                                                             s  in
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
                                                               (uu___149_368.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___149_368.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___149_368.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___149_368.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard1)))))))))))
      | uu____373 -> failwith "impossible"
  
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
            let uu____433 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____433 with
             | (usubst,_uvs1) ->
                 let uu____456 =
                   let uu____461 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____462 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____461, uu____462)  in
                 (match uu____456 with
                  | (env1,t1) ->
                      let uu____469 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____508  ->
                               match uu____508 with
                               | (se1,u_tc) ->
                                   let uu____523 =
                                     let uu____524 =
                                       let uu____525 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____525  in
                                     FStar_Ident.lid_equals tc_lid uu____524
                                      in
                                   if uu____523
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____544,uu____545,tps,uu____547,uu____548,uu____549)
                                          ->
                                          let tps1 =
                                            let uu____559 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____559
                                              (FStar_List.map
                                                 (fun uu____585  ->
                                                    match uu____585 with
                                                    | (x,uu____597) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____601 =
                                            let uu____608 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____608, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____601
                                      | uu____615 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____656 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____656
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____469 with
                       | (env2,tps,u_tc) ->
                           let uu____681 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____695 =
                               let uu____696 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____696.FStar_Syntax_Syntax.n  in
                             match uu____695 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____729 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____729 with
                                  | (uu____762,bs') ->
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
                                                fun uu____819  ->
                                                  match uu____819 with
                                                  | (x,uu____825) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____826 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____826)
                             | uu____827 -> ([], t2)  in
                           (match uu____681 with
                            | (arguments,result) ->
                                ((let uu____861 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____861
                                  then
                                    let uu____862 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____863 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____864 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____862 uu____863 uu____864
                                  else ());
                                 (let uu____866 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____866 with
                                  | (arguments1,env',us) ->
                                      let uu____880 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____880 with
                                       | (result1,res_lcomp) ->
                                           ((let uu____892 =
                                               let uu____893 =
                                                 FStar_Syntax_Subst.compress
                                                   res_lcomp.FStar_Syntax_Syntax.res_typ
                                                  in
                                               uu____893.FStar_Syntax_Syntax.n
                                                in
                                             match uu____892 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____896 -> ()
                                             | ty ->
                                                 let uu____898 =
                                                   let uu____903 =
                                                     let uu____904 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____905 =
                                                       FStar_Syntax_Print.term_to_string
                                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____904 uu____905
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____903)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____898
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____906 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____906 with
                                             | (head1,uu____926) ->
                                                 let g_uvs =
                                                   let uu____948 =
                                                     let uu____949 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____949.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____948 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____953;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____954;_},tuvs)
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
                                                                  let uu____967
                                                                    =
                                                                    let uu____968
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____969
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
                                                                    uu____968
                                                                    uu____969
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g
                                                                    uu____967)
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
                                                   | uu____972 ->
                                                       let uu____973 =
                                                         let uu____978 =
                                                           let uu____979 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____980 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____979
                                                             uu____980
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____978)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____973
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____993  ->
                                                          fun u_x  ->
                                                            match uu____993
                                                            with
                                                            | (x,uu____1000)
                                                                ->
                                                                let uu____1001
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g
                                                                  uu____1001)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1005 =
                                                     let uu____1012 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1044 
                                                               ->
                                                               match uu____1044
                                                               with
                                                               | (x,uu____1056)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1012 arguments1
                                                      in
                                                   let uu____1063 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1005 uu____1063
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___150_1068 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___150_1068.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___150_1068.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___150_1068.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___150_1068.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1071 -> failwith "impossible"
  
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
            let uu___151_1136 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___151_1136.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___151_1136.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___151_1136.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1146 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1146
           then
             let uu____1147 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1147
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1183  ->
                     match uu____1183 with
                     | (se,uu____1189) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1190,uu____1191,tps,k,uu____1194,uu____1195)
                              ->
                              let uu____1204 =
                                let uu____1205 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1205
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1204
                          | uu____1210 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1234,uu____1235,t,uu____1237,uu____1238,uu____1239)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1244 -> failwith "Impossible"))
              in
           let t =
             let uu____1248 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1248
              in
           (let uu____1256 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1256
            then
              let uu____1257 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1257
            else ());
           (let uu____1259 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1259 with
            | (uvs,t1) ->
                ((let uu____1279 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1279
                  then
                    let uu____1280 =
                      let uu____1281 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1281
                        (FStar_String.concat ", ")
                       in
                    let uu____1292 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1280 uu____1292
                  else ());
                 (let uu____1294 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1294 with
                  | (uvs1,t2) ->
                      let uu____1309 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1309 with
                       | (args,uu____1331) ->
                           let uu____1348 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1348 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1435  ->
                                       fun uu____1436  ->
                                         match (uu____1435, uu____1436) with
                                         | ((x,uu____1454),(se,uu____1456))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1466,tps,uu____1468,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1480 =
                                                    let uu____1493 =
                                                      let uu____1494 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1494.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1493 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1527 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1527
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1599
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1622 -> ([], ty)
                                                     in
                                                  (match uu____1480 with
                                                   | (tps1,t3) ->
                                                       let uu___152_1651 = se
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
                                                           (uu___152_1651.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___152_1651.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___152_1651.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___152_1651.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1656 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1662 ->
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
                                             (fun uu___140_1684  ->
                                                match uu___140_1684 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1690,uu____1691,uu____1692,uu____1693,uu____1694);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1695;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1696;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1697;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1698;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1711 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1732  ->
                                           fun d  ->
                                             match uu____1732 with
                                             | (t3,uu____1739) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1741,uu____1742,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1751 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1751
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___153_1752 = d
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
                                                          (uu___153_1752.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___153_1752.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___153_1752.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___153_1752.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1755 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1770 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1770
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1782 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1782
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1798 =
      let uu____1799 = FStar_Syntax_Subst.compress t  in
      uu____1799.FStar_Syntax_Syntax.n  in
    match uu____1798 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1818 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1823 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1876 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1945  ->
               match uu____1945 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1980 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1980  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1876
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2200 =
             let uu____2201 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2201
              in
           debug_log env uu____2200);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
              in
           (let uu____2204 =
              let uu____2205 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2205
               in
            debug_log env uu____2204);
           (let uu____2208 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2208) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2219 =
                  let uu____2220 = FStar_Syntax_Subst.compress btype1  in
                  uu____2220.FStar_Syntax_Syntax.n  in
                match uu____2219 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2245 = try_get_fv t  in
                    (match uu____2245 with
                     | (fv,us) ->
                         let uu____2252 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2252
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2262  ->
                                 match uu____2262 with
                                 | (t1,uu____2268) ->
                                     let uu____2269 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2269) args)
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
                          let uu____2315 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2315
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2319 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2319
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
                            (fun uu____2337  ->
                               match uu____2337 with
                               | (b,uu____2343) ->
                                   let uu____2344 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2344) sbs)
                           &&
                           ((let uu____2349 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2349 with
                             | (uu____2354,return_type) ->
                                 let uu____2356 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2356)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2377 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2379 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2382) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2409) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2435,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2493  ->
                          match uu____2493 with
                          | (p,uu____2505,t) ->
                              let bs =
                                let uu____2522 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2522
                                 in
                              let uu____2529 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2529 with
                               | (bs1,t1) ->
                                   let uu____2536 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2536)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2558,uu____2559)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2621 ->
                    ((let uu____2623 =
                        let uu____2624 =
                          let uu____2625 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2626 =
                            let uu____2627 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2627  in
                          Prims.strcat uu____2625 uu____2626  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2624
                         in
                      debug_log env uu____2623);
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
              (let uu____2645 =
                 let uu____2646 =
                   let uu____2647 =
                     let uu____2648 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2648  in
                   Prims.strcat ilid.FStar_Ident.str uu____2647  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2646
                  in
               debug_log env uu____2645);
              (let uu____2649 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2649 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2664 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2664
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2689 =
                            let uu____2690 =
                              let uu____2691 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2691
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2690
                             in
                          debug_log env uu____2689);
                         (let uu____2693 =
                            let uu____2694 = FStar_ST.op_Bang unfolded  in
                            let uu____2744 =
                              let uu____2751 =
                                let uu____2756 =
                                  let uu____2757 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2757  in
                                (ilid, uu____2756)  in
                              [uu____2751]  in
                            FStar_List.append uu____2694 uu____2744  in
                          FStar_ST.op_Colon_Equals unfolded uu____2693);
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
                  (let uu____2896 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2896 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2918 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Normalize.Iota;
                             FStar_TypeChecker_Normalize.Zeta;
                             FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                             env dt
                            in
                         (let uu____2921 =
                            let uu____2922 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2922
                             in
                          debug_log env uu____2921);
                         (let uu____2923 =
                            let uu____2924 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2924.FStar_Syntax_Syntax.n  in
                          match uu____2923 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2946 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2946 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____2995 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2995 dbs1
                                       in
                                    let c1 =
                                      let uu____2999 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2999 c
                                       in
                                    let uu____3002 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3002 with
                                     | (args1,uu____3030) ->
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
                                           let uu____3102 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3102 c1
                                            in
                                         ((let uu____3110 =
                                             let uu____3111 =
                                               let uu____3112 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3113 =
                                                 let uu____3114 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3114
                                                  in
                                               Prims.strcat uu____3112
                                                 uu____3113
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3111
                                              in
                                           debug_log env uu____3110);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3143 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3145 =
                                  let uu____3146 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3146.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3145
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
                   (let uu____3208 = try_get_fv t1  in
                    match uu____3208 with
                    | (fv,uu____3214) ->
                        let uu____3215 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3215
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3236 =
                      let uu____3237 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3237
                       in
                    debug_log env uu____3236);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3239 =
                      FStar_List.fold_left
                        (fun uu____3256  ->
                           fun b  ->
                             match uu____3256 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3277 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3298 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3277, uu____3298))) (true, env)
                        sbs1
                       in
                    match uu____3239 with | (b,uu____3308) -> b))
              | uu____3309 ->
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
              let uu____3360 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3360 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3382 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3384 =
                      let uu____3385 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3385
                       in
                    debug_log env uu____3384);
                   (let uu____3386 =
                      let uu____3387 = FStar_Syntax_Subst.compress dt  in
                      uu____3387.FStar_Syntax_Syntax.n  in
                    match uu____3386 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3390 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3393) ->
                        let dbs1 =
                          let uu____3417 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3417  in
                        let dbs2 =
                          let uu____3455 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3455 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3460 =
                            let uu____3461 =
                              let uu____3462 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3462 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3461
                             in
                          debug_log env uu____3460);
                         (let uu____3467 =
                            FStar_List.fold_left
                              (fun uu____3484  ->
                                 fun b  ->
                                   match uu____3484 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3505 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3526 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3505, uu____3526)))
                              (true, env) dbs3
                             in
                          match uu____3467 with | (b,uu____3536) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3537,uu____3538) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3587 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3605 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3621,uu____3622,uu____3623) -> (lid, us, bs)
        | uu____3632 -> failwith "Impossible!"  in
      match uu____3605 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3642 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3642 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3665 =
                 let uu____3668 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3668  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3680 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3680
                      unfolded_inductives env2) uu____3665)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3710,uu____3711,t,uu____3713,uu____3714,uu____3715) -> t
    | uu____3720 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3740 =
         let uu____3741 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3741 haseq_suffix  in
       uu____3740 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3761 =
      let uu____3764 =
        let uu____3767 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3767]  in
      FStar_List.append lid.FStar_Ident.ns uu____3764  in
    FStar_Ident.lid_of_ids uu____3761
  
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
          let uu____3812 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3826,bs,t,uu____3829,uu____3830) -> (lid, bs, t)
            | uu____3839 -> failwith "Impossible!"  in
          match uu____3812 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3861 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3861 t  in
              let uu____3868 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3868 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3886 =
                       let uu____3887 = FStar_Syntax_Subst.compress t2  in
                       uu____3887.FStar_Syntax_Syntax.n  in
                     match uu____3886 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3891) -> ibs
                     | uu____3908 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3915 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3916 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3915 uu____3916
                      in
                   let ind1 =
                     let uu____3922 =
                       let uu____3927 =
                         FStar_List.map
                           (fun uu____3940  ->
                              match uu____3940 with
                              | (bv,aq) ->
                                  let uu____3951 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3951, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3927  in
                     uu____3922 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3957 =
                       let uu____3962 =
                         FStar_List.map
                           (fun uu____3975  ->
                              match uu____3975 with
                              | (bv,aq) ->
                                  let uu____3986 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3986, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3962  in
                     uu____3957 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____3992 =
                       let uu____3997 =
                         let uu____3998 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____3998]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____3997
                        in
                     uu____3992 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4037 =
                            let uu____4038 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4038  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4037) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4049 =
                              let uu____4052 =
                                let uu____4057 =
                                  let uu____4058 =
                                    let uu____4065 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4065  in
                                  [uu____4058]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4057
                                 in
                              uu____4052 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4049)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___154_4084 = fml  in
                     let uu____4085 =
                       let uu____4086 =
                         let uu____4093 =
                           let uu____4094 =
                             let uu____4105 =
                               let uu____4114 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4114]  in
                             [uu____4105]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4094  in
                         (fml, uu____4093)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4086  in
                     {
                       FStar_Syntax_Syntax.n = uu____4085;
                       FStar_Syntax_Syntax.pos =
                         (uu___154_4084.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___154_4084.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4159 =
                              let uu____4164 =
                                let uu____4165 =
                                  let uu____4172 =
                                    let uu____4173 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4173 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4172  in
                                [uu____4165]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4164
                               in
                            uu____4159 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4214 =
                              let uu____4219 =
                                let uu____4220 =
                                  let uu____4227 =
                                    let uu____4228 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4228 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4227  in
                                [uu____4220]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4219
                               in
                            uu____4214 FStar_Pervasives_Native.None
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
          let uu____4288 =
            let uu____4289 = FStar_Syntax_Subst.compress dt1  in
            uu____4289.FStar_Syntax_Syntax.n  in
          match uu____4288 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4293) ->
              let dbs1 =
                let uu____4317 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4317  in
              let dbs2 =
                let uu____4355 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4355 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4370 =
                           let uu____4375 =
                             let uu____4376 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4376]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4375
                            in
                         uu____4370 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4399 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4399 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4407 =
                       let uu____4412 =
                         let uu____4413 =
                           let uu____4420 =
                             let uu____4421 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4421
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4420  in
                         [uu____4413]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4412
                        in
                     uu____4407 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4454 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple4 ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
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
                  (lid,uu____4544,uu____4545,uu____4546,uu____4547,uu____4548)
                  -> lid
              | uu____4557 -> failwith "Impossible!"  in
            let uu____4558 = acc  in
            match uu____4558 with
            | (uu____4595,en,uu____4597,uu____4598) ->
                let uu____4619 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4619 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4656 = acc  in
                     (match uu____4656 with
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
                                     (uu____4730,uu____4731,uu____4732,t_lid,uu____4734,uu____4735)
                                     -> t_lid = lid
                                 | uu____4740 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4753 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4753)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4756 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4759 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4756, uu____4759)))
  
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
                (uu____4818,us,uu____4820,uu____4821,uu____4822,uu____4823)
                -> us
            | uu____4832 -> failwith "Impossible!"  in
          let uu____4833 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4833 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4858 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4858 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4936 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4936 with
                     | (phi1,uu____4944) ->
                         ((let uu____4946 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4946
                           then
                             let uu____4947 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4947
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4964  ->
                                    match uu____4964 with
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
                let uu____5032 =
                  let uu____5033 = FStar_Syntax_Subst.compress t  in
                  uu____5033.FStar_Syntax_Syntax.n  in
                match uu____5032 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5040) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5073 = is_mutual t'  in
                    if uu____5073
                    then true
                    else
                      (let uu____5075 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5075)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5091) -> is_mutual t'
                | uu____5096 -> false
              
              and exists_mutual uu___141_5097 =
                match uu___141_5097 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5116 =
                let uu____5117 = FStar_Syntax_Subst.compress dt1  in
                uu____5117.FStar_Syntax_Syntax.n  in
              match uu____5116 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5123) ->
                  let dbs1 =
                    let uu____5147 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5147  in
                  let dbs2 =
                    let uu____5185 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5185 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5203 =
                               let uu____5208 =
                                 let uu____5209 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5209]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5208
                                in
                             uu____5203 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5233 = is_mutual sort  in
                             if uu____5233
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
                           let uu____5245 =
                             let uu____5250 =
                               let uu____5251 =
                                 let uu____5258 =
                                   let uu____5259 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5259 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5258  in
                               [uu____5251]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5250
                              in
                           uu____5245 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5292 -> acc
  
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
              let uu____5341 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5363,bs,t,uu____5366,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5378 -> failwith "Impossible!"  in
              match uu____5341 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5401 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5401 t  in
                  let uu____5408 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5408 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5418 =
                           let uu____5419 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5419.FStar_Syntax_Syntax.n  in
                         match uu____5418 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5423) ->
                             ibs
                         | uu____5440 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5447 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5448 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5447
                           uu____5448
                          in
                       let ind1 =
                         let uu____5454 =
                           let uu____5459 =
                             FStar_List.map
                               (fun uu____5472  ->
                                  match uu____5472 with
                                  | (bv,aq) ->
                                      let uu____5483 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5483, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5459  in
                         uu____5454 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5489 =
                           let uu____5494 =
                             FStar_List.map
                               (fun uu____5507  ->
                                  match uu____5507 with
                                  | (bv,aq) ->
                                      let uu____5518 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5518, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5494  in
                         uu____5489 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5524 =
                           let uu____5529 =
                             let uu____5530 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5530]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5529
                            in
                         uu____5524 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5562,uu____5563,uu____5564,t_lid,uu____5566,uu____5567)
                                  -> t_lid = lid
                              | uu____5572 -> failwith "Impossible")
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
                         let uu___155_5582 = fml  in
                         let uu____5583 =
                           let uu____5584 =
                             let uu____5591 =
                               let uu____5592 =
                                 let uu____5603 =
                                   let uu____5612 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5612]  in
                                 [uu____5603]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5592
                                in
                             (fml, uu____5591)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5584  in
                         {
                           FStar_Syntax_Syntax.n = uu____5583;
                           FStar_Syntax_Syntax.pos =
                             (uu___155_5582.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___155_5582.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5657 =
                                  let uu____5662 =
                                    let uu____5663 =
                                      let uu____5670 =
                                        let uu____5671 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5671
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5670
                                       in
                                    [uu____5663]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5662
                                   in
                                uu____5657 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5712 =
                                  let uu____5717 =
                                    let uu____5718 =
                                      let uu____5725 =
                                        let uu____5726 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5726
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5725
                                       in
                                    [uu____5718]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5717
                                   in
                                uu____5712 FStar_Pervasives_Native.None
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
                     (lid,uu____5803,uu____5804,uu____5805,uu____5806,uu____5807)
                     -> lid
                 | uu____5816 -> failwith "Impossible!") tcs
             in
          let uu____5817 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5829,uu____5830,uu____5831,uu____5832) ->
                (lid, us)
            | uu____5841 -> failwith "Impossible!"  in
          match uu____5817 with
          | (lid,us) ->
              let uu____5850 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5850 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5877 =
                       let uu____5878 =
                         let uu____5885 = get_haseq_axiom_lid lid  in
                         (uu____5885, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5878  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5877;
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
          let uu____5938 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___142_5963  ->
                    match uu___142_5963 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5964;
                        FStar_Syntax_Syntax.sigrng = uu____5965;
                        FStar_Syntax_Syntax.sigquals = uu____5966;
                        FStar_Syntax_Syntax.sigmeta = uu____5967;
                        FStar_Syntax_Syntax.sigattrs = uu____5968;_} -> true
                    | uu____5989 -> false))
             in
          match uu____5938 with
          | (tys,datas) ->
              ((let uu____6011 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___143_6020  ->
                          match uu___143_6020 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6021;
                              FStar_Syntax_Syntax.sigrng = uu____6022;
                              FStar_Syntax_Syntax.sigquals = uu____6023;
                              FStar_Syntax_Syntax.sigmeta = uu____6024;
                              FStar_Syntax_Syntax.sigattrs = uu____6025;_} ->
                              false
                          | uu____6044 -> true))
                   in
                if uu____6011
                then
                  let uu____6045 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6045
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6054 =
                       let uu____6055 = FStar_List.hd tys  in
                       uu____6055.FStar_Syntax_Syntax.sigel  in
                     match uu____6054 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6058,uvs,uu____6060,uu____6061,uu____6062,uu____6063)
                         -> uvs
                     | uu____6072 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6076 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6103 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6103 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6141,bs,t,l1,l2) ->
                                      let uu____6154 =
                                        let uu____6171 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6172 =
                                          let uu____6173 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6173
                                            t
                                           in
                                        (lid, univs2, uu____6171, uu____6172,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6154
                                  | uu____6184 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___156_6185 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___156_6185.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___156_6185.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___156_6185.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___156_6185.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6195,t,lid_t,x,l) ->
                                      let uu____6204 =
                                        let uu____6219 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6219, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6204
                                  | uu____6222 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___157_6223 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___157_6223.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___157_6223.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___157_6223.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___157_6223.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6224 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6224, tys1, datas1))
                   in
                match uu____6076 with
                | (env1,tys1,datas1) ->
                    let uu____6250 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6289  ->
                             match uu____6289 with
                             | (env2,all_tcs,g) ->
                                 let uu____6329 = tc_tycon env2 tc  in
                                 (match uu____6329 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____6356 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____6356
                                        then
                                          let uu____6357 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____6357
                                        else ());
                                       (let uu____6359 =
                                          let uu____6360 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____6360
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____6359))))) tys1
                        (env1, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____6250 with
                     | (env2,tcs,g) ->
                         let uu____6406 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____6428  ->
                                  match uu____6428 with
                                  | (datas2,g1) ->
                                      let uu____6447 =
                                        let uu____6452 = tc_data env2 tcs  in
                                        uu____6452 se  in
                                      (match uu____6447 with
                                       | (data,g') ->
                                           let uu____6469 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____6469)))
                             datas1 ([], g)
                            in
                         (match uu____6406 with
                          | (datas2,g1) ->
                              let uu____6490 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____6509 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____6509, datas2))
                                 in
                              (match uu____6490 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____6541 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____6542 =
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
                                         uu____6541;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____6542
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____6568,uu____6569)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6589 =
                                                    let uu____6594 =
                                                      let uu____6595 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6596 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6595 uu____6596
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6594)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6589
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6597 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6597 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6613)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6640 ->
                                                             let uu____6641 =
                                                               let uu____6648
                                                                 =
                                                                 let uu____6649
                                                                   =
                                                                   let uu____6662
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6662)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6649
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6648
                                                                in
                                                             uu____6641
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
                                                       let uu____6682 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6682 with
                                                        | (uu____6687,inferred)
                                                            ->
                                                            let uu____6689 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6689
                                                             with
                                                             | (uu____6694,expected)
                                                                 ->
                                                                 let uu____6696
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6696
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6699 -> ()));
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
                          let uu____6791 =
                            let uu____6798 =
                              let uu____6799 =
                                let uu____6806 =
                                  let uu____6809 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6809  in
                                (uu____6806, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6799  in
                            FStar_Syntax_Syntax.mk uu____6798  in
                          uu____6791 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6838  ->
                                  match uu____6838 with
                                  | (x,imp) ->
                                      let uu____6849 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6849, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6851 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6851  in
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
                               let uu____6868 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6868
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6869 =
                               let uu____6872 =
                                 let uu____6875 =
                                   let uu____6880 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6881 =
                                     let uu____6882 =
                                       let uu____6889 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6889
                                        in
                                     [uu____6882]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6880
                                     uu____6881
                                    in
                                 uu____6875 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6872  in
                             FStar_Syntax_Util.refine x uu____6869  in
                           let uu____6910 =
                             let uu___158_6911 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_6911.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_6911.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6910)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6926 =
                          FStar_List.map
                            (fun uu____6948  ->
                               match uu____6948 with
                               | (x,uu____6960) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6926 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7005  ->
                                match uu____7005 with
                                | (x,uu____7017) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7023 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7023)
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
                               (let uu____7036 =
                                  let uu____7037 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7037.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7036)
                              in
                           let quals =
                             let uu____7041 =
                               FStar_List.filter
                                 (fun uu___144_7045  ->
                                    match uu___144_7045 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7046 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7041
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7071 =
                                 let uu____7072 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7072  in
                               FStar_Syntax_Syntax.mk_Total uu____7071  in
                             let uu____7073 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7073
                              in
                           let decl =
                             let uu____7075 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7075;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7077 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7077
                            then
                              let uu____7078 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7078
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
                                             fun uu____7129  ->
                                               match uu____7129 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7153 =
                                                       let uu____7156 =
                                                         let uu____7157 =
                                                           let uu____7164 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7164,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7157
                                                          in
                                                       pos uu____7156  in
                                                     (uu____7153, b)
                                                   else
                                                     (let uu____7170 =
                                                        let uu____7173 =
                                                          let uu____7174 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7174
                                                           in
                                                        pos uu____7173  in
                                                      (uu____7170, b))))
                                      in
                                   let pat_true =
                                     let uu____7192 =
                                       let uu____7195 =
                                         let uu____7196 =
                                           let uu____7209 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7209, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7196
                                          in
                                       pos uu____7195  in
                                     (uu____7192,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7243 =
                                       let uu____7246 =
                                         let uu____7247 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7247
                                          in
                                       pos uu____7246  in
                                     (uu____7243,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____7259 =
                                     let uu____7266 =
                                       let uu____7267 =
                                         let uu____7290 =
                                           let uu____7307 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7322 =
                                             let uu____7339 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7339]  in
                                           uu____7307 :: uu____7322  in
                                         (arg_exp, uu____7290)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7267
                                        in
                                     FStar_Syntax_Syntax.mk uu____7266  in
                                   uu____7259 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____7418 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7418
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
                                let uu____7432 =
                                  let uu____7437 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____7437  in
                                let uu____7438 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____7432
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____7438 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____7444 =
                                  let uu____7445 =
                                    let uu____7452 =
                                      let uu____7455 =
                                        let uu____7456 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____7456
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____7455]  in
                                    ((false, [lb]), uu____7452)  in
                                  FStar_Syntax_Syntax.Sig_let uu____7445  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7444;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____7468 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7468
                               then
                                 let uu____7469 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7469
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
                                fun uu____7521  ->
                                  match uu____7521 with
                                  | (a,uu____7527) ->
                                      let uu____7528 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7528 with
                                       | (field_name,uu____7534) ->
                                           let field_proj_tm =
                                             let uu____7536 =
                                               let uu____7537 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7537
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7536 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7558 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7596  ->
                                    match uu____7596 with
                                    | (x,uu____7604) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7606 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7606 with
                                         | (field_name,uu____7614) ->
                                             let t =
                                               let uu____7618 =
                                                 let uu____7619 =
                                                   let uu____7622 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7622
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7619
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7618
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____7627 =
                                                    let uu____7628 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7628.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7627)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7644 =
                                                   FStar_List.filter
                                                     (fun uu___145_7648  ->
                                                        match uu___145_7648
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7649 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7644
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___146_7662  ->
                                                         match uu___146_7662
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7663 ->
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
                                               let uu____7675 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____7675;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____7677 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7677
                                               then
                                                 let uu____7678 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7678
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
                                                           fun uu____7724  ->
                                                             match uu____7724
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
                                                                   let uu____7748
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7748,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7764
                                                                    =
                                                                    let uu____7767
                                                                    =
                                                                    let uu____7768
                                                                    =
                                                                    let uu____7775
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7775,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7768
                                                                     in
                                                                    pos
                                                                    uu____7767
                                                                     in
                                                                    (uu____7764,
                                                                    b))
                                                                   else
                                                                    (let uu____7781
                                                                    =
                                                                    let uu____7784
                                                                    =
                                                                    let uu____7785
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7785
                                                                     in
                                                                    pos
                                                                    uu____7784
                                                                     in
                                                                    (uu____7781,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7803 =
                                                     let uu____7806 =
                                                       let uu____7807 =
                                                         let uu____7820 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____7820,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7807
                                                        in
                                                     pos uu____7806  in
                                                   let uu____7829 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7803,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7829)
                                                    in
                                                 let body =
                                                   let uu____7845 =
                                                     let uu____7852 =
                                                       let uu____7853 =
                                                         let uu____7876 =
                                                           let uu____7893 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7893]  in
                                                         (arg_exp,
                                                           uu____7876)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7853
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7852
                                                      in
                                                   uu____7845
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____7961 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7961
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
                                                   let uu____7972 =
                                                     let uu____7977 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7977
                                                      in
                                                   let uu____7978 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7972;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7978;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____7984 =
                                                     let uu____7985 =
                                                       let uu____7992 =
                                                         let uu____7995 =
                                                           let uu____7996 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____7996
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____7995]  in
                                                       ((false, [lb]),
                                                         uu____7992)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7985
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7984;
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
                                                 (let uu____8008 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8008
                                                  then
                                                    let uu____8009 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8009
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7558 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8057) when
              let uu____8062 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8062 ->
              let uu____8063 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8063 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8085 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8085 with
                    | (formals,uu____8101) ->
                        let uu____8118 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8150 =
                                   let uu____8151 =
                                     let uu____8152 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8152  in
                                   FStar_Ident.lid_equals typ_lid uu____8151
                                    in
                                 if uu____8150
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8171,uvs',tps,typ0,uu____8175,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8192 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____8233 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____8233
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8118 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8258 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____8258 with
                              | (indices,uu____8274) ->
                                  let refine_domain =
                                    let uu____8292 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___147_8297  ->
                                              match uu___147_8297 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8298 -> true
                                              | uu____8307 -> false))
                                       in
                                    if uu____8292
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___148_8317 =
                                      match uu___148_8317 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8320,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8332 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____8333 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____8333 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____8344 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8344 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8409  ->
                                               fun uu____8410  ->
                                                 match (uu____8409,
                                                         uu____8410)
                                                 with
                                                 | ((x,uu____8428),(x',uu____8430))
                                                     ->
                                                     let uu____8439 =
                                                       let uu____8446 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8446)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8439) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8451 -> []
  