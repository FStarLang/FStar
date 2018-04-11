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
          let uu____38 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____38 with
           | (usubst,uvs1) ->
               let uu____65 =
                 let uu____72 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____73 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____74 =
                   let uu____75 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____75 k  in
                 (uu____72, uu____73, uu____74)  in
               (match uu____65 with
                | (env1,tps1,k1) ->
                    let uu____93 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____93 with
                     | (tps2,k2) ->
                         let uu____108 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____108 with
                          | (tps3,env_tps,guard_params,us) ->
                              let k3 =
                                FStar_TypeChecker_Normalize.unfold_whnf env1
                                  k2
                                 in
                              let uu____130 =
                                FStar_Syntax_Util.arrow_formals k3  in
                              (match uu____130 with
                               | (indices,t) ->
                                   let uu____169 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____169 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____190 =
                                          let uu____195 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____195 with
                                          | (t1,uu____207,g) ->
                                              let uu____209 =
                                                let uu____210 =
                                                  let uu____211 =
                                                    FStar_TypeChecker_Rel.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    guard_params uu____211
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____210
                                                 in
                                              (t1, uu____209)
                                           in
                                        (match uu____190 with
                                         | (t1,guard) ->
                                             let k4 =
                                               let uu____225 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____225
                                                in
                                             let uu____228 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____228 with
                                              | (t_type,u) ->
                                                  ((let uu____244 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env' t1 t_type
                                                       in
                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                      env' uu____244);
                                                   (let usubst1 =
                                                      FStar_Syntax_Subst.univ_var_closing
                                                        uvs1
                                                       in
                                                    let t_tc =
                                                      let uu____251 =
                                                        let uu____258 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____265 =
                                                          let uu____272 =
                                                            let uu____275 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____275
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____272
                                                           in
                                                        FStar_List.append
                                                          uu____258 uu____265
                                                         in
                                                      let uu____286 =
                                                        let uu____289 =
                                                          let uu____290 =
                                                            let uu____293 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____293
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____290
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____289
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____251 uu____286
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k5 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k4
                                                       in
                                                    let uu____306 =
                                                      let uu____311 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____312 =
                                                        let uu____313 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____313 k5
                                                         in
                                                      (uu____311, uu____312)
                                                       in
                                                    match uu____306 with
                                                    | (tps5,k6) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.Delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____331 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____331,
                                                          (let uu___71_337 =
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
                                                               (uu___71_337.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___71_337.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___71_337.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___71_337.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard)))))))))))
      | uu____344 -> failwith "impossible"
  
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
            let uu____398 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____398 with
             | (usubst,_uvs1) ->
                 let uu____421 =
                   let uu____426 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____427 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____426, uu____427)  in
                 (match uu____421 with
                  | (env1,t1) ->
                      let uu____434 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____473  ->
                               match uu____473 with
                               | (se1,u_tc) ->
                                   let uu____488 =
                                     let uu____489 =
                                       let uu____490 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____490  in
                                     FStar_Ident.lid_equals tc_lid uu____489
                                      in
                                   if uu____488
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____509,uu____510,tps,uu____512,uu____513,uu____514)
                                          ->
                                          let tps1 =
                                            let uu____532 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____532
                                              (FStar_List.map
                                                 (fun uu____554  ->
                                                    match uu____554 with
                                                    | (x,uu____566) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____570 =
                                            let uu____577 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____577, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____570
                                      | uu____584 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____625 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____625
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____434 with
                       | (env2,tps,u_tc) ->
                           let uu____656 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____670 =
                               let uu____671 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____671.FStar_Syntax_Syntax.n  in
                             match uu____670 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____704 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____704 with
                                  | (uu____737,bs') ->
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
                                                fun uu____788  ->
                                                  match uu____788 with
                                                  | (x,uu____794) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____795 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____795)
                             | uu____796 -> ([], t2)  in
                           (match uu____656 with
                            | (arguments,result) ->
                                ((let uu____830 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____830
                                  then
                                    let uu____831 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____832 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____833 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____831 uu____832 uu____833
                                  else ());
                                 (let uu____835 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____835 with
                                  | (arguments1,env',us) ->
                                      let uu____849 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____849 with
                                       | (result1,res_lcomp) ->
                                           ((let uu____861 =
                                               let uu____862 =
                                                 FStar_Syntax_Subst.compress
                                                   res_lcomp.FStar_Syntax_Syntax.res_typ
                                                  in
                                               uu____862.FStar_Syntax_Syntax.n
                                                in
                                             match uu____861 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____865 -> ()
                                             | ty ->
                                                 let uu____867 =
                                                   let uu____872 =
                                                     let uu____873 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____874 =
                                                       FStar_Syntax_Print.term_to_string
                                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____873 uu____874
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____872)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____867
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____875 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____875 with
                                             | (head1,uu____895) ->
                                                 let g_uvs =
                                                   let uu____917 =
                                                     let uu____918 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____918.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____917 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____922;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____923;_},tuvs)
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
                                                                  let uu____936
                                                                    =
                                                                    let uu____937
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____938
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
                                                                    uu____937
                                                                    uu____938
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g
                                                                    uu____936)
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
                                                   | uu____941 ->
                                                       let uu____942 =
                                                         let uu____947 =
                                                           let uu____948 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____949 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____948
                                                             uu____949
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____947)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____942
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____962  ->
                                                          fun u_x  ->
                                                            match uu____962
                                                            with
                                                            | (x,uu____969)
                                                                ->
                                                                let uu____970
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g uu____970)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____974 =
                                                     let uu____981 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1011 
                                                               ->
                                                               match uu____1011
                                                               with
                                                               | (x,uu____1023)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____981 arguments1
                                                      in
                                                   let uu____1032 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____974 uu____1032
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___72_1037 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___72_1037.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___72_1037.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___72_1037.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___72_1037.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1042 -> failwith "impossible"
  
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
            let uu___73_1099 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___73_1099.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___73_1099.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___73_1099.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1109 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1109
           then
             let uu____1110 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1110
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1138  ->
                     match uu____1138 with
                     | (se,uu____1144) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1145,uu____1146,tps,k,uu____1149,uu____1150)
                              ->
                              let uu____1159 =
                                let uu____1160 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1160
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1159
                          | uu____1167 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1183,uu____1184,t,uu____1186,uu____1187,uu____1188)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1193 -> failwith "Impossible"))
              in
           let t =
             let uu____1197 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1197
              in
           (let uu____1201 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1201
            then
              let uu____1202 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1202
            else ());
           (let uu____1204 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1204 with
            | (uvs,t1) ->
                ((let uu____1220 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1220
                  then
                    let uu____1221 =
                      let uu____1222 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1222
                        (FStar_String.concat ", ")
                       in
                    let uu____1233 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1221 uu____1233
                  else ());
                 (let uu____1235 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1235 with
                  | (uvs1,t2) ->
                      let uu____1250 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1250 with
                       | (args,uu____1272) ->
                           let uu____1289 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1289 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1372  ->
                                       fun uu____1373  ->
                                         match (uu____1372, uu____1373) with
                                         | ((x,uu____1391),(se,uu____1393))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1403,tps,uu____1405,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1417 =
                                                    let uu____1430 =
                                                      let uu____1431 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1431.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1430 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1464 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1464
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1536
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1559 -> ([], ty)
                                                     in
                                                  (match uu____1417 with
                                                   | (tps1,t3) ->
                                                       let uu___74_1588 = se
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
                                                           (uu___74_1588.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___74_1588.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___74_1588.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___74_1588.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1601 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1607 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___62_1649  ->
                                                match uu___62_1649 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1657,uu____1658,uu____1659,uu____1660,uu____1661);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1662;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1663;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1664;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1665;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1680 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1703  ->
                                           fun d  ->
                                             match uu____1703 with
                                             | (t3,uu____1710) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1712,uu____1713,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1722 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1722
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___75_1723 = d
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
                                                          (uu___75_1723.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___75_1723.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___75_1723.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___75_1723.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1726 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit) =
  fun env  ->
    fun s  ->
      let uu____1737 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1737
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1745 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1745
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1759 =
      let uu____1760 = FStar_Syntax_Subst.compress t  in
      uu____1760.FStar_Syntax_Syntax.n  in
    match uu____1759 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1781 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1786 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref[@@deriving show]
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1831 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1896  ->
               match uu____1896 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1931 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1931  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1831
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2103 =
             let uu____2104 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2104
              in
           debug_log env uu____2103);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype
              in
           (let uu____2107 =
              let uu____2108 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2108
               in
            debug_log env uu____2107);
           (let uu____2111 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2111) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2122 =
                  let uu____2123 = FStar_Syntax_Subst.compress btype1  in
                  uu____2123.FStar_Syntax_Syntax.n  in
                match uu____2122 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2148 = try_get_fv t  in
                    (match uu____2148 with
                     | (fv,us) ->
                         let uu____2155 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2155
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2165  ->
                                 match uu____2165 with
                                 | (t1,uu____2171) ->
                                     let uu____2172 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2172) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2214 =
                        let uu____2215 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____2215  in
                      if uu____2214
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2227  ->
                               match uu____2227 with
                               | (b,uu____2233) ->
                                   let uu____2234 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2234) sbs)
                           &&
                           ((let uu____2239 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2239 with
                             | (uu____2244,return_type) ->
                                 let uu____2246 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2246)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2267 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2269 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2272) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2299) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2325,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2383  ->
                          match uu____2383 with
                          | (p,uu____2395,t) ->
                              let bs =
                                let uu____2408 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2408
                                 in
                              let uu____2411 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2411 with
                               | (bs1,t1) ->
                                   let uu____2418 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2418)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2440,uu____2441)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2503 ->
                    ((let uu____2505 =
                        let uu____2506 =
                          let uu____2507 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2508 =
                            let uu____2509 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2509  in
                          Prims.strcat uu____2507 uu____2508  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2506
                         in
                      debug_log env uu____2505);
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
              (let uu____2527 =
                 let uu____2528 =
                   let uu____2529 =
                     let uu____2530 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2530  in
                   Prims.strcat ilid.FStar_Ident.str uu____2529  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2528
                  in
               debug_log env uu____2527);
              (let uu____2531 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2531 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2546 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2546
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2571 =
                            let uu____2572 =
                              let uu____2573 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2573
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2572
                             in
                          debug_log env uu____2571);
                         (let uu____2575 =
                            let uu____2576 = FStar_ST.op_Bang unfolded  in
                            let uu____2622 =
                              let uu____2629 =
                                let uu____2642 =
                                  let uu____2651 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2651  in
                                (ilid, uu____2642)  in
                              [uu____2629]  in
                            FStar_List.append uu____2576 uu____2622  in
                          FStar_ST.op_Colon_Equals unfolded uu____2575);
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
                  (let uu____2810 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2810 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2832 ->
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
                             env dt
                            in
                         (let uu____2835 =
                            let uu____2836 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2836
                             in
                          debug_log env uu____2835);
                         (let uu____2837 =
                            let uu____2838 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2838.FStar_Syntax_Syntax.n  in
                          match uu____2837 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2860 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2860 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____2909 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2909 dbs1
                                       in
                                    let c1 =
                                      let uu____2913 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2913 c
                                       in
                                    let uu____2916 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____2916 with
                                     | (args1,uu____2944) ->
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
                                           let uu____3016 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3016 c1
                                            in
                                         ((let uu____3024 =
                                             let uu____3025 =
                                               let uu____3026 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3027 =
                                                 let uu____3028 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3028
                                                  in
                                               Prims.strcat uu____3026
                                                 uu____3027
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3025
                                              in
                                           debug_log env uu____3024);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3049 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3051 =
                                  let uu____3052 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3052.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3051
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
                   (let uu____3114 = try_get_fv t1  in
                    match uu____3114 with
                    | (fv,uu____3120) ->
                        let uu____3121 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3121
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3142 =
                      let uu____3143 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3143
                       in
                    debug_log env uu____3142);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3145 =
                      FStar_List.fold_left
                        (fun uu____3162  ->
                           fun b  ->
                             match uu____3162 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3183 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3204 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3183, uu____3204))) (true, env)
                        sbs1
                       in
                    match uu____3145 with | (b,uu____3214) -> b))
              | uu____3215 ->
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
              let uu____3254 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3254 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3276 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3278 =
                      let uu____3279 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3279
                       in
                    debug_log env uu____3278);
                   (let uu____3280 =
                      let uu____3281 = FStar_Syntax_Subst.compress dt  in
                      uu____3281.FStar_Syntax_Syntax.n  in
                    match uu____3280 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3284 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3287) ->
                        let dbs1 =
                          let uu____3311 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3311  in
                        let dbs2 =
                          let uu____3349 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3349 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3354 =
                            let uu____3355 =
                              let uu____3356 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3356 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3355
                             in
                          debug_log env uu____3354);
                         (let uu____3361 =
                            FStar_List.fold_left
                              (fun uu____3378  ->
                                 fun b  ->
                                   match uu____3378 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3399 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3420 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3399, uu____3420)))
                              (true, env) dbs3
                             in
                          match uu____3361 with | (b,uu____3430) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3431,uu____3432) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3481 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3507 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3523,uu____3524,uu____3525) -> (lid, us, bs)
        | uu____3534 -> failwith "Impossible!"  in
      match uu____3507 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3544 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3544 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3567 =
                 let uu____3570 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3570  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3582 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3582
                      unfolded_inductives env2) uu____3567)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3610,uu____3611,t,uu____3613,uu____3614,uu____3615) -> t
    | uu____3620 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3638 =
         let uu____3639 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3639 haseq_suffix  in
       uu____3638 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3657 =
      let uu____3660 =
        let uu____3663 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3663]  in
      FStar_List.append lid.FStar_Ident.ns uu____3660  in
    FStar_Ident.lid_of_ids uu____3657
  
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
          let uu____3700 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3714,bs,t,uu____3717,uu____3718) -> (lid, bs, t)
            | uu____3727 -> failwith "Impossible!"  in
          match uu____3700 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3749 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3749 t  in
              let uu____3756 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3756 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3780 =
                       let uu____3781 = FStar_Syntax_Subst.compress t2  in
                       uu____3781.FStar_Syntax_Syntax.n  in
                     match uu____3780 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3791) -> ibs
                     | uu____3808 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3815 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3816 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3815 uu____3816
                      in
                   let ind1 =
                     let uu____3822 =
                       let uu____3823 =
                         FStar_List.map
                           (fun uu____3836  ->
                              match uu____3836 with
                              | (bv,aq) ->
                                  let uu____3847 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3847, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3823  in
                     uu____3822 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3853 =
                       let uu____3854 =
                         FStar_List.map
                           (fun uu____3867  ->
                              match uu____3867 with
                              | (bv,aq) ->
                                  let uu____3878 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3878, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3854  in
                     uu____3853 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____3884 =
                       let uu____3885 =
                         let uu____3886 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____3886]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____3885
                        in
                     uu____3884 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____3907 =
                            let uu____3908 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____3908  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____3907) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____3919 =
                              let uu____3920 =
                                let uu____3921 =
                                  let uu____3922 =
                                    let uu____3923 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____3923  in
                                  [uu____3922]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____3921
                                 in
                              uu____3920 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____3919)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___76_3930 = fml  in
                     let uu____3931 =
                       let uu____3932 =
                         let uu____3939 =
                           let uu____3940 =
                             let uu____3951 =
                               let uu____3954 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____3954]  in
                             [uu____3951]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____3940  in
                         (fml, uu____3939)  in
                       FStar_Syntax_Syntax.Tm_meta uu____3932  in
                     {
                       FStar_Syntax_Syntax.n = uu____3931;
                       FStar_Syntax_Syntax.pos =
                         (uu___76_3930.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___76_3930.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____3967 =
                              let uu____3968 =
                                let uu____3969 =
                                  let uu____3970 =
                                    let uu____3971 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____3971 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____3970  in
                                [uu____3969]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____3968
                               in
                            uu____3967 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____3996 =
                              let uu____3997 =
                                let uu____3998 =
                                  let uu____3999 =
                                    let uu____4000 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4000 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____3999  in
                                [uu____3998]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____3997
                               in
                            uu____3996 FStar_Pervasives_Native.None
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
          let uu____4036 =
            let uu____4037 = FStar_Syntax_Subst.compress dt1  in
            uu____4037.FStar_Syntax_Syntax.n  in
          match uu____4036 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4041) ->
              let dbs1 =
                let uu____4065 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4065  in
              let dbs2 =
                let uu____4103 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4103 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4118 =
                           let uu____4119 =
                             let uu____4120 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4120]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4119
                            in
                         uu____4118 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4125 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4125 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4133 =
                       let uu____4134 =
                         let uu____4135 =
                           let uu____4136 =
                             let uu____4137 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4137
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4136  in
                         [uu____4135]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4134
                        in
                     uu____4133 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4154 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
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
                  (lid,uu____4226,uu____4227,uu____4228,uu____4229,uu____4230)
                  -> lid
              | uu____4239 -> failwith "Impossible!"  in
            let uu____4240 = acc  in
            match uu____4240 with
            | (uu____4273,en,uu____4275,uu____4276) ->
                let uu____4289 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4289 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4326 = acc  in
                     (match uu____4326 with
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
                                     (uu____4388,uu____4389,uu____4390,t_lid,uu____4392,uu____4393)
                                     -> t_lid = lid
                                 | uu____4398 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4405 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4405)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4406 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4409 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4406, uu____4409)))
  
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
                (uu____4460,us,uu____4462,uu____4463,uu____4464,uu____4465)
                -> us
            | uu____4474 -> failwith "Impossible!"  in
          let uu____4475 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4475 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4500 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4500 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4558 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4558 with
                     | (phi1,uu____4566) ->
                         ((let uu____4568 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4568
                           then
                             let uu____4569 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4569
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4586  ->
                                    match uu____4586 with
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
                let uu____4640 =
                  let uu____4641 = FStar_Syntax_Subst.compress t  in
                  uu____4641.FStar_Syntax_Syntax.n  in
                match uu____4640 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4648) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4681 = is_mutual t'  in
                    if uu____4681
                    then true
                    else
                      (let uu____4683 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____4683)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4699) -> is_mutual t'
                | uu____4704 -> false
              
              and exists_mutual uu___63_4705 =
                match uu___63_4705 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____4724 =
                let uu____4725 = FStar_Syntax_Subst.compress dt1  in
                uu____4725.FStar_Syntax_Syntax.n  in
              match uu____4724 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4731) ->
                  let dbs1 =
                    let uu____4755 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____4755  in
                  let dbs2 =
                    let uu____4793 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____4793 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____4811 =
                               let uu____4812 =
                                 let uu____4813 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____4813]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4812
                                in
                             uu____4811 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____4817 = is_mutual sort  in
                             if uu____4817
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
                           let uu____4827 =
                             let uu____4828 =
                               let uu____4829 =
                                 let uu____4830 =
                                   let uu____4831 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4831 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____4830  in
                               [uu____4829]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4828
                              in
                           uu____4827 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4848 -> acc
  
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
              let uu____4885 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4907,bs,t,uu____4910,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4922 -> failwith "Impossible!"  in
              match uu____4885 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____4945 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____4945 t  in
                  let uu____4952 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____4952 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4968 =
                           let uu____4969 = FStar_Syntax_Subst.compress t2
                              in
                           uu____4969.FStar_Syntax_Syntax.n  in
                         match uu____4968 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4979) ->
                             ibs
                         | uu____4996 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5003 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5004 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5003
                           uu____5004
                          in
                       let ind1 =
                         let uu____5010 =
                           let uu____5011 =
                             FStar_List.map
                               (fun uu____5024  ->
                                  match uu____5024 with
                                  | (bv,aq) ->
                                      let uu____5035 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5035, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5011  in
                         uu____5010 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5041 =
                           let uu____5042 =
                             FStar_List.map
                               (fun uu____5055  ->
                                  match uu____5055 with
                                  | (bv,aq) ->
                                      let uu____5066 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5066, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5042  in
                         uu____5041 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5072 =
                           let uu____5073 =
                             let uu____5074 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5074]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5073
                            in
                         uu____5072 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5088,uu____5089,uu____5090,t_lid,uu____5092,uu____5093)
                                  -> t_lid = lid
                              | uu____5098 -> failwith "Impossible")
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
                         let uu___77_5104 = fml  in
                         let uu____5105 =
                           let uu____5106 =
                             let uu____5113 =
                               let uu____5114 =
                                 let uu____5125 =
                                   let uu____5128 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5128]  in
                                 [uu____5125]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5114
                                in
                             (fml, uu____5113)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5106  in
                         {
                           FStar_Syntax_Syntax.n = uu____5105;
                           FStar_Syntax_Syntax.pos =
                             (uu___77_5104.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___77_5104.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5141 =
                                  let uu____5142 =
                                    let uu____5143 =
                                      let uu____5144 =
                                        let uu____5145 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5145
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5144
                                       in
                                    [uu____5143]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5142
                                   in
                                uu____5141 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5170 =
                                  let uu____5171 =
                                    let uu____5172 =
                                      let uu____5173 =
                                        let uu____5174 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5174
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5173
                                       in
                                    [uu____5172]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5171
                                   in
                                uu____5170 FStar_Pervasives_Native.None
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
                     (lid,uu____5227,uu____5228,uu____5229,uu____5230,uu____5231)
                     -> lid
                 | uu____5240 -> failwith "Impossible!") tcs
             in
          let uu____5241 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5253,uu____5254,uu____5255,uu____5256) ->
                (lid, us)
            | uu____5265 -> failwith "Impossible!"  in
          match uu____5241 with
          | (lid,us) ->
              let uu____5274 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5274 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5297 =
                       let uu____5298 =
                         let uu____5305 = get_haseq_axiom_lid lid  in
                         (uu____5305, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5298  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5297;
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
          let uu____5352 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___64_5377  ->
                    match uu___64_5377 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5378;
                        FStar_Syntax_Syntax.sigrng = uu____5379;
                        FStar_Syntax_Syntax.sigquals = uu____5380;
                        FStar_Syntax_Syntax.sigmeta = uu____5381;
                        FStar_Syntax_Syntax.sigattrs = uu____5382;_} -> true
                    | uu____5403 -> false))
             in
          match uu____5352 with
          | (tys,datas) ->
              ((let uu____5425 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___65_5434  ->
                          match uu___65_5434 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5435;
                              FStar_Syntax_Syntax.sigrng = uu____5436;
                              FStar_Syntax_Syntax.sigquals = uu____5437;
                              FStar_Syntax_Syntax.sigmeta = uu____5438;
                              FStar_Syntax_Syntax.sigattrs = uu____5439;_} ->
                              false
                          | uu____5458 -> true))
                   in
                if uu____5425
                then
                  let uu____5459 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____5459
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____5467 =
                       let uu____5468 = FStar_List.hd tys  in
                       uu____5468.FStar_Syntax_Syntax.sigel  in
                     match uu____5467 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____5471,uvs,uu____5473,uu____5474,uu____5475,uu____5476)
                         -> uvs
                     | uu____5485 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____5489 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____5515 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____5515 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____5553,bs,t,l1,l2) ->
                                      let uu____5566 =
                                        let uu____5583 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____5584 =
                                          let uu____5585 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____5585
                                            t
                                           in
                                        (lid, univs2, uu____5583, uu____5584,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____5566
                                  | uu____5598 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___78_5599 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___78_5599.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___78_5599.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___78_5599.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___78_5599.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____5609,t,lid_t,x,l) ->
                                      let uu____5618 =
                                        let uu____5633 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____5633, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____5618
                                  | uu____5638 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___79_5639 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___79_5639.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___79_5639.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___79_5639.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___79_5639.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____5640 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____5640, tys1, datas1))
                   in
                match uu____5489 with
                | (env1,tys1,datas1) ->
                    let uu____5666 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____5705  ->
                             match uu____5705 with
                             | (env2,all_tcs,g) ->
                                 let uu____5745 = tc_tycon env2 tc  in
                                 (match uu____5745 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____5772 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____5772
                                        then
                                          let uu____5773 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____5773
                                        else ());
                                       (let uu____5775 =
                                          let uu____5776 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____5776
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____5775))))) tys1
                        (env1, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____5666 with
                     | (env2,tcs,g) ->
                         let uu____5822 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____5844  ->
                                  match uu____5844 with
                                  | (datas2,g1) ->
                                      let uu____5863 =
                                        let uu____5868 = tc_data env2 tcs  in
                                        uu____5868 se  in
                                      (match uu____5863 with
                                       | (data,g') ->
                                           let uu____5883 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____5883)))
                             datas1 ([], g)
                            in
                         (match uu____5822 with
                          | (datas2,g1) ->
                              let uu____5904 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____5922 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____5922, datas2))
                                 in
                              (match uu____5904 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____5954 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____5955 =
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
                                         uu____5954;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____5955
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____5981,uu____5982)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____5998 =
                                                    let uu____6003 =
                                                      let uu____6004 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6005 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6004 uu____6005
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6003)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5998
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6006 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6006 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6022)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6043 ->
                                                             let uu____6044 =
                                                               let uu____6047
                                                                 =
                                                                 let uu____6048
                                                                   =
                                                                   let uu____6061
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6061)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6048
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6047
                                                                in
                                                             uu____6044
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
                                                       let uu____6067 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6067 with
                                                        | (uu____6072,inferred)
                                                            ->
                                                            let uu____6074 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6074
                                                             with
                                                             | (uu____6079,expected)
                                                                 ->
                                                                 let uu____6081
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6081
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6084 -> ()));
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
                          let uu____6152 =
                            let uu____6155 =
                              let uu____6156 =
                                let uu____6163 =
                                  let uu____6164 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6164  in
                                (uu____6163, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6156  in
                            FStar_Syntax_Syntax.mk uu____6155  in
                          uu____6152 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6205  ->
                                  match uu____6205 with
                                  | (x,imp) ->
                                      let uu____6216 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6216, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6218 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6218  in
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
                               let uu____6227 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6227
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6228 =
                               let uu____6229 =
                                 let uu____6230 =
                                   let uu____6231 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6232 =
                                     let uu____6233 =
                                       let uu____6234 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6234
                                        in
                                     [uu____6233]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6231
                                     uu____6232
                                    in
                                 uu____6230 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6229  in
                             FStar_Syntax_Util.refine x uu____6228  in
                           let uu____6237 =
                             let uu___80_6238 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___80_6238.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___80_6238.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6237)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6253 =
                          FStar_List.map
                            (fun uu____6275  ->
                               match uu____6275 with
                               | (x,uu____6287) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6253 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6336  ->
                                match uu____6336 with
                                | (x,uu____6348) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____6354 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____6354)
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
                               (let uu____6367 =
                                  let uu____6368 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____6368.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____6367)
                              in
                           let quals =
                             let uu____6372 =
                               FStar_List.filter
                                 (fun uu___66_6376  ->
                                    match uu___66_6376 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____6377 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____6372
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____6398 =
                                 let uu____6399 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____6399  in
                               FStar_Syntax_Syntax.mk_Total uu____6398  in
                             let uu____6400 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____6400
                              in
                           let decl =
                             let uu____6402 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____6402;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____6404 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____6404
                            then
                              let uu____6405 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____6405
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
                                             fun uu____6458  ->
                                               match uu____6458 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____6482 =
                                                       let uu____6485 =
                                                         let uu____6486 =
                                                           let uu____6493 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____6493,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____6486
                                                          in
                                                       pos uu____6485  in
                                                     (uu____6482, b)
                                                   else
                                                     (let uu____6497 =
                                                        let uu____6500 =
                                                          let uu____6501 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____6501
                                                           in
                                                        pos uu____6500  in
                                                      (uu____6497, b))))
                                      in
                                   let pat_true =
                                     let uu____6519 =
                                       let uu____6522 =
                                         let uu____6523 =
                                           let uu____6536 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____6536, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____6523
                                          in
                                       pos uu____6522  in
                                     (uu____6519,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____6570 =
                                       let uu____6573 =
                                         let uu____6574 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____6574
                                          in
                                       pos uu____6573  in
                                     (uu____6570,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____6586 =
                                     let uu____6589 =
                                       let uu____6590 =
                                         let uu____6613 =
                                           let uu____6616 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____6617 =
                                             let uu____6620 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____6620]  in
                                           uu____6616 :: uu____6617  in
                                         (arg_exp, uu____6613)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____6590
                                        in
                                     FStar_Syntax_Syntax.mk uu____6589  in
                                   uu____6586 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____6627 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____6627
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____6635 =
                                  let uu____6640 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____6640  in
                                let uu____6641 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____6635
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____6641 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____6647 =
                                  let uu____6648 =
                                    let uu____6655 =
                                      let uu____6658 =
                                        let uu____6659 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____6659
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____6658]  in
                                    ((false, [lb]), uu____6655)  in
                                  FStar_Syntax_Syntax.Sig_let uu____6648  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____6647;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____6677 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____6677
                               then
                                 let uu____6678 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____6678
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
                                fun uu____6720  ->
                                  match uu____6720 with
                                  | (a,uu____6726) ->
                                      let uu____6727 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____6727 with
                                       | (field_name,uu____6733) ->
                                           let field_proj_tm =
                                             let uu____6735 =
                                               let uu____6736 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____6736
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____6735 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____6753 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____6785  ->
                                    match uu____6785 with
                                    | (x,uu____6793) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____6795 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____6795 with
                                         | (field_name,uu____6803) ->
                                             let t =
                                               let uu____6805 =
                                                 let uu____6806 =
                                                   let uu____6809 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____6809
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____6806
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____6805
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____6812 =
                                                    let uu____6813 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____6813.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____6812)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____6827 =
                                                   FStar_List.filter
                                                     (fun uu___67_6831  ->
                                                        match uu___67_6831
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____6832 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____6827
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___68_6845  ->
                                                         match uu___68_6845
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____6846 ->
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
                                               let uu____6864 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____6864;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____6866 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____6866
                                               then
                                                 let uu____6867 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____6867
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
                                                           fun uu____6915  ->
                                                             match uu____6915
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
                                                                   let uu____6939
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____6939,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____6955
                                                                    =
                                                                    let uu____6958
                                                                    =
                                                                    let uu____6959
                                                                    =
                                                                    let uu____6966
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____6966,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____6959
                                                                     in
                                                                    pos
                                                                    uu____6958
                                                                     in
                                                                    (uu____6955,
                                                                    b))
                                                                   else
                                                                    (let uu____6970
                                                                    =
                                                                    let uu____6973
                                                                    =
                                                                    let uu____6974
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____6974
                                                                     in
                                                                    pos
                                                                    uu____6973
                                                                     in
                                                                    (uu____6970,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____6990 =
                                                     let uu____6993 =
                                                       let uu____6994 =
                                                         let uu____7007 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____7007,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____6994
                                                        in
                                                     pos uu____6993  in
                                                   let uu____7016 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____6990,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7016)
                                                    in
                                                 let body =
                                                   let uu____7028 =
                                                     let uu____7031 =
                                                       let uu____7032 =
                                                         let uu____7055 =
                                                           let uu____7058 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7058]  in
                                                         (arg_exp,
                                                           uu____7055)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7032
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7031
                                                      in
                                                   uu____7028
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____7066 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7066
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____7073 =
                                                     let uu____7078 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7078
                                                      in
                                                   let uu____7079 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7073;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7079;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____7085 =
                                                     let uu____7086 =
                                                       let uu____7093 =
                                                         let uu____7096 =
                                                           let uu____7097 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____7097
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____7096]  in
                                                       ((false, [lb]),
                                                         uu____7093)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7086
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7085;
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
                                                 (let uu____7115 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7115
                                                  then
                                                    let uu____7116 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7116
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____6753 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____7156) when
              let uu____7161 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____7161 ->
              let uu____7162 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____7162 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____7184 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____7184 with
                    | (formals,uu____7200) ->
                        let uu____7217 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____7249 =
                                   let uu____7250 =
                                     let uu____7251 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____7251  in
                                   FStar_Ident.lid_equals typ_lid uu____7250
                                    in
                                 if uu____7249
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____7270,uvs',tps,typ0,uu____7274,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____7293 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____7334 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____7334
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____7217 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____7367 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____7367 with
                              | (indices,uu____7383) ->
                                  let refine_domain =
                                    let uu____7401 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___69_7406  ->
                                              match uu___69_7406 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____7407 -> true
                                              | uu____7416 -> false))
                                       in
                                    if uu____7401
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___70_7424 =
                                      match uu___70_7424 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____7427,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____7439 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____7440 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____7440 with
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
                                    let uu____7451 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____7451 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____7516  ->
                                               fun uu____7517  ->
                                                 match (uu____7516,
                                                         uu____7517)
                                                 with
                                                 | ((x,uu____7535),(x',uu____7537))
                                                     ->
                                                     let uu____7546 =
                                                       let uu____7553 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____7553)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____7546) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____7554 -> []
  