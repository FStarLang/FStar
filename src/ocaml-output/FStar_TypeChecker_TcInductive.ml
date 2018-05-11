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
                                          let uu____201 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____201 with
                                          | (t1,uu____215,g) ->
                                              let uu____217 =
                                                let uu____218 =
                                                  let uu____219 =
                                                    FStar_TypeChecker_Rel.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    guard_params uu____219
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____218
                                                 in
                                              (t1, uu____217)
                                           in
                                        (match uu____194 with
                                         | (t1,guard) ->
                                             let k4 =
                                               let uu____239 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____239
                                                in
                                             let uu____242 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____242 with
                                              | (t_type,u) ->
                                                  ((let uu____258 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env' t1 t_type
                                                       in
                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                      env' uu____258);
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
                                                      let uu____270 =
                                                        let uu____277 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____290 =
                                                          let uu____297 =
                                                            let uu____308 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____308
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____297
                                                           in
                                                        FStar_List.append
                                                          uu____277 uu____290
                                                         in
                                                      let uu____325 =
                                                        let uu____328 =
                                                          let uu____329 =
                                                            let uu____334 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____334
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____329
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____328
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____270 uu____325
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k5 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k4
                                                       in
                                                    let uu____347 =
                                                      let uu____352 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____353 =
                                                        let uu____354 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____354 k5
                                                         in
                                                      (uu____352, uu____353)
                                                       in
                                                    match uu____347 with
                                                    | (tps5,k6) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____372 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____372,
                                                          (let uu___95_378 =
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
                                                               (uu___95_378.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___95_378.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___95_378.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___95_378.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard1)))))))))))
      | uu____383 -> failwith "impossible"
  
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
            let uu____443 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____443 with
             | (usubst,_uvs1) ->
                 let uu____466 =
                   let uu____471 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____472 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____471, uu____472)  in
                 (match uu____466 with
                  | (env1,t1) ->
                      let uu____479 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____518  ->
                               match uu____518 with
                               | (se1,u_tc) ->
                                   let uu____533 =
                                     let uu____534 =
                                       let uu____535 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____535  in
                                     FStar_Ident.lid_equals tc_lid uu____534
                                      in
                                   if uu____533
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____554,uu____555,tps,uu____557,uu____558,uu____559)
                                          ->
                                          let tps1 =
                                            let uu____569 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____569
                                              (FStar_List.map
                                                 (fun uu____601  ->
                                                    match uu____601 with
                                                    | (x,uu____613) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____617 =
                                            let uu____624 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____624, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____617
                                      | uu____631 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____672 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____672
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____479 with
                       | (env2,tps,u_tc) ->
                           let uu____697 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____711 =
                               let uu____712 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____712.FStar_Syntax_Syntax.n  in
                             match uu____711 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____745 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____745 with
                                  | (uu____778,bs') ->
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
                                                fun uu____835  ->
                                                  match uu____835 with
                                                  | (x,uu____841) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____842 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____842)
                             | uu____843 -> ([], t2)  in
                           (match uu____697 with
                            | (arguments,result) ->
                                ((let uu____879 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____879
                                  then
                                    let uu____880 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____881 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____882 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____880 uu____881 uu____882
                                  else ());
                                 (let uu____884 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____884 with
                                  | (arguments1,env',us) ->
                                      let uu____898 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____898 with
                                       | (result1,res_lcomp) ->
                                           ((let uu____910 =
                                               let uu____911 =
                                                 FStar_Syntax_Subst.compress
                                                   res_lcomp.FStar_Syntax_Syntax.res_typ
                                                  in
                                               uu____911.FStar_Syntax_Syntax.n
                                                in
                                             match uu____910 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____914 -> ()
                                             | ty ->
                                                 let uu____916 =
                                                   let uu____921 =
                                                     let uu____922 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____923 =
                                                       FStar_Syntax_Print.term_to_string
                                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____922 uu____923
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____921)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____916
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____924 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____924 with
                                             | (head1,uu____944) ->
                                                 let g_uvs =
                                                   let uu____966 =
                                                     let uu____967 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____967.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____966 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____971;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____972;_},tuvs)
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
                                                                  let uu____985
                                                                    =
                                                                    let uu____986
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____987
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
                                                                    uu____986
                                                                    uu____987
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g
                                                                    uu____985)
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
                                                   | uu____990 ->
                                                       let uu____991 =
                                                         let uu____996 =
                                                           let uu____997 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____998 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____997
                                                             uu____998
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____996)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____991
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____1011  ->
                                                          fun u_x  ->
                                                            match uu____1011
                                                            with
                                                            | (x,uu____1018)
                                                                ->
                                                                let uu____1019
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g
                                                                  uu____1019)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1023 =
                                                     let uu____1030 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1062 
                                                               ->
                                                               match uu____1062
                                                               with
                                                               | (x,uu____1074)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1030 arguments1
                                                      in
                                                   let uu____1081 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1023 uu____1081
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___96_1086 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___96_1086.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___96_1086.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___96_1086.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___96_1086.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1089 -> failwith "impossible"
  
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
            let uu___97_1154 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___97_1154.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___97_1154.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___97_1154.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1164 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1164
           then
             let uu____1165 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1165
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1201  ->
                     match uu____1201 with
                     | (se,uu____1207) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1208,uu____1209,tps,k,uu____1212,uu____1213)
                              ->
                              let uu____1222 =
                                let uu____1223 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1223
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1222
                          | uu____1228 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1252,uu____1253,t,uu____1255,uu____1256,uu____1257)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1262 -> failwith "Impossible"))
              in
           let t =
             let uu____1266 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1266
              in
           (let uu____1274 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1274
            then
              let uu____1275 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1275
            else ());
           (let uu____1277 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1277 with
            | (uvs,t1) ->
                ((let uu____1297 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1297
                  then
                    let uu____1298 =
                      let uu____1299 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1299
                        (FStar_String.concat ", ")
                       in
                    let uu____1310 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1298 uu____1310
                  else ());
                 (let uu____1312 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1312 with
                  | (uvs1,t2) ->
                      let uu____1327 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1327 with
                       | (args,uu____1349) ->
                           let uu____1366 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1366 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1453  ->
                                       fun uu____1454  ->
                                         match (uu____1453, uu____1454) with
                                         | ((x,uu____1472),(se,uu____1474))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1484,tps,uu____1486,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1498 =
                                                    let uu____1503 =
                                                      let uu____1504 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1504.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1503 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1529 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1529
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1589
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1604 -> ([], ty)
                                                     in
                                                  (match uu____1498 with
                                                   | (tps1,t3) ->
                                                       let uu___98_1611 = se
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
                                                           (uu___98_1611.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___98_1611.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___98_1611.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___98_1611.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1616 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1622 ->
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
                                             (fun uu___86_1644  ->
                                                match uu___86_1644 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1650,uu____1651,uu____1652,uu____1653,uu____1654);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1655;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1656;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1657;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1658;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1671 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1692  ->
                                           fun d  ->
                                             match uu____1692 with
                                             | (t3,uu____1699) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1701,uu____1702,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1711 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1711
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___99_1712 = d
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
                                                          (uu___99_1712.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___99_1712.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___99_1712.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___99_1712.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1715 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1730 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1730
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1742 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1742
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1758 =
      let uu____1759 = FStar_Syntax_Subst.compress t  in
      uu____1759.FStar_Syntax_Syntax.n  in
    match uu____1758 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1778 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1783 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1836 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1905  ->
               match uu____1905 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1940 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1940  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1836
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2160 =
             let uu____2161 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2161
              in
           debug_log env uu____2160);
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
           (let uu____2164 =
              let uu____2165 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2165
               in
            debug_log env uu____2164);
           (let uu____2168 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2168) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2179 =
                  let uu____2180 = FStar_Syntax_Subst.compress btype1  in
                  uu____2180.FStar_Syntax_Syntax.n  in
                match uu____2179 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2205 = try_get_fv t  in
                    (match uu____2205 with
                     | (fv,us) ->
                         let uu____2212 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2212
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2222  ->
                                 match uu____2222 with
                                 | (t1,uu____2228) ->
                                     let uu____2229 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2229) args)
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
                          let uu____2275 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2275
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2279 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2279
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
                            (fun uu____2297  ->
                               match uu____2297 with
                               | (b,uu____2303) ->
                                   let uu____2304 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2304) sbs)
                           &&
                           ((let uu____2309 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2309 with
                             | (uu____2314,return_type) ->
                                 let uu____2316 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2316)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2337 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2339 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2342) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2369) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2395,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2453  ->
                          match uu____2453 with
                          | (p,uu____2465,t) ->
                              let bs =
                                let uu____2482 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2482
                                 in
                              let uu____2489 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2489 with
                               | (bs1,t1) ->
                                   let uu____2496 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2496)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2518,uu____2519)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2581 ->
                    ((let uu____2583 =
                        let uu____2584 =
                          let uu____2585 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2586 =
                            let uu____2587 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2587  in
                          Prims.strcat uu____2585 uu____2586  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2584
                         in
                      debug_log env uu____2583);
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
              (let uu____2605 =
                 let uu____2606 =
                   let uu____2607 =
                     let uu____2608 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2608  in
                   Prims.strcat ilid.FStar_Ident.str uu____2607  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2606
                  in
               debug_log env uu____2605);
              (let uu____2609 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2609 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2624 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2624
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2649 =
                            let uu____2650 =
                              let uu____2651 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2651
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2650
                             in
                          debug_log env uu____2649);
                         (let uu____2653 =
                            let uu____2654 = FStar_ST.op_Bang unfolded  in
                            let uu____2704 =
                              let uu____2711 =
                                let uu____2716 =
                                  let uu____2717 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2717  in
                                (ilid, uu____2716)  in
                              [uu____2711]  in
                            FStar_List.append uu____2654 uu____2704  in
                          FStar_ST.op_Colon_Equals unfolded uu____2653);
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
                  (let uu____2856 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2856 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2878 ->
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
                         (let uu____2881 =
                            let uu____2882 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2882
                             in
                          debug_log env uu____2881);
                         (let uu____2883 =
                            let uu____2884 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2884.FStar_Syntax_Syntax.n  in
                          match uu____2883 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2906 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2906 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____2955 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2955 dbs1
                                       in
                                    let c1 =
                                      let uu____2959 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2959 c
                                       in
                                    let uu____2962 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____2962 with
                                     | (args1,uu____2990) ->
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
                                           let uu____3062 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3062 c1
                                            in
                                         ((let uu____3070 =
                                             let uu____3071 =
                                               let uu____3072 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3073 =
                                                 let uu____3074 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3074
                                                  in
                                               Prims.strcat uu____3072
                                                 uu____3073
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3071
                                              in
                                           debug_log env uu____3070);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3103 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3105 =
                                  let uu____3106 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3106.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3105
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
                   (let uu____3168 = try_get_fv t1  in
                    match uu____3168 with
                    | (fv,uu____3174) ->
                        let uu____3175 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3175
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3196 =
                      let uu____3197 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3197
                       in
                    debug_log env uu____3196);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3199 =
                      FStar_List.fold_left
                        (fun uu____3216  ->
                           fun b  ->
                             match uu____3216 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3237 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3258 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3237, uu____3258))) (true, env)
                        sbs1
                       in
                    match uu____3199 with | (b,uu____3268) -> b))
              | uu____3269 ->
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
              let uu____3320 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3320 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3342 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3344 =
                      let uu____3345 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3345
                       in
                    debug_log env uu____3344);
                   (let uu____3346 =
                      let uu____3347 = FStar_Syntax_Subst.compress dt  in
                      uu____3347.FStar_Syntax_Syntax.n  in
                    match uu____3346 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3350 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3353) ->
                        let dbs1 =
                          let uu____3377 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3377  in
                        let dbs2 =
                          let uu____3415 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3415 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3420 =
                            let uu____3421 =
                              let uu____3422 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3422 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3421
                             in
                          debug_log env uu____3420);
                         (let uu____3427 =
                            FStar_List.fold_left
                              (fun uu____3444  ->
                                 fun b  ->
                                   match uu____3444 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3465 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3486 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3465, uu____3486)))
                              (true, env) dbs3
                             in
                          match uu____3427 with | (b,uu____3496) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3497,uu____3498) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3547 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3565 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3581,uu____3582,uu____3583) -> (lid, us, bs)
        | uu____3592 -> failwith "Impossible!"  in
      match uu____3565 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3602 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3602 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3625 =
                 let uu____3628 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3628  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3640 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3640
                      unfolded_inductives env2) uu____3625)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3670,uu____3671,t,uu____3673,uu____3674,uu____3675) -> t
    | uu____3680 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3700 =
         let uu____3701 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3701 haseq_suffix  in
       uu____3700 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3721 =
      let uu____3724 =
        let uu____3727 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3727]  in
      FStar_List.append lid.FStar_Ident.ns uu____3724  in
    FStar_Ident.lid_of_ids uu____3721
  
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
          let uu____3772 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3786,bs,t,uu____3789,uu____3790) -> (lid, bs, t)
            | uu____3799 -> failwith "Impossible!"  in
          match uu____3772 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3821 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3821 t  in
              let uu____3828 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3828 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3846 =
                       let uu____3847 = FStar_Syntax_Subst.compress t2  in
                       uu____3847.FStar_Syntax_Syntax.n  in
                     match uu____3846 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3851) -> ibs
                     | uu____3868 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3875 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3876 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3875 uu____3876
                      in
                   let ind1 =
                     let uu____3882 =
                       let uu____3887 =
                         FStar_List.map
                           (fun uu____3900  ->
                              match uu____3900 with
                              | (bv,aq) ->
                                  let uu____3911 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3911, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3887  in
                     uu____3882 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3917 =
                       let uu____3922 =
                         FStar_List.map
                           (fun uu____3935  ->
                              match uu____3935 with
                              | (bv,aq) ->
                                  let uu____3946 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3946, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3922  in
                     uu____3917 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____3952 =
                       let uu____3957 =
                         let uu____3958 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____3958]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____3957
                        in
                     uu____3952 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____3997 =
                            let uu____3998 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____3998  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____3997) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4009 =
                              let uu____4012 =
                                let uu____4017 =
                                  let uu____4018 =
                                    let uu____4025 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4025  in
                                  [uu____4018]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4017
                                 in
                              uu____4012 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4009)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___100_4044 = fml  in
                     let uu____4045 =
                       let uu____4046 =
                         let uu____4053 =
                           let uu____4054 =
                             let uu____4065 =
                               let uu____4074 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4074]  in
                             [uu____4065]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4054  in
                         (fml, uu____4053)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4046  in
                     {
                       FStar_Syntax_Syntax.n = uu____4045;
                       FStar_Syntax_Syntax.pos =
                         (uu___100_4044.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___100_4044.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4119 =
                              let uu____4124 =
                                let uu____4125 =
                                  let uu____4132 =
                                    let uu____4133 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4133 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4132  in
                                [uu____4125]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4124
                               in
                            uu____4119 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4174 =
                              let uu____4179 =
                                let uu____4180 =
                                  let uu____4187 =
                                    let uu____4188 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4188 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4187  in
                                [uu____4180]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4179
                               in
                            uu____4174 FStar_Pervasives_Native.None
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
          let uu____4248 =
            let uu____4249 = FStar_Syntax_Subst.compress dt1  in
            uu____4249.FStar_Syntax_Syntax.n  in
          match uu____4248 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4253) ->
              let dbs1 =
                let uu____4277 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4277  in
              let dbs2 =
                let uu____4315 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4315 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4330 =
                           let uu____4335 =
                             let uu____4336 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4336]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4335
                            in
                         uu____4330 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4359 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4359 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4367 =
                       let uu____4372 =
                         let uu____4373 =
                           let uu____4380 =
                             let uu____4381 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4381
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4380  in
                         [uu____4373]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4372
                        in
                     uu____4367 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4414 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____4504,uu____4505,uu____4506,uu____4507,uu____4508)
                  -> lid
              | uu____4517 -> failwith "Impossible!"  in
            let uu____4518 = acc  in
            match uu____4518 with
            | (uu____4555,en,uu____4557,uu____4558) ->
                let uu____4579 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4579 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4616 = acc  in
                     (match uu____4616 with
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
                                     (uu____4690,uu____4691,uu____4692,t_lid,uu____4694,uu____4695)
                                     -> t_lid = lid
                                 | uu____4700 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4713 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4713)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4716 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4719 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4716, uu____4719)))
  
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
                (uu____4778,us,uu____4780,uu____4781,uu____4782,uu____4783)
                -> us
            | uu____4792 -> failwith "Impossible!"  in
          let uu____4793 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4793 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4818 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4818 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4896 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4896 with
                     | (phi1,uu____4904) ->
                         ((let uu____4906 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4906
                           then
                             let uu____4907 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4907
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4924  ->
                                    match uu____4924 with
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
                let uu____4992 =
                  let uu____4993 = FStar_Syntax_Subst.compress t  in
                  uu____4993.FStar_Syntax_Syntax.n  in
                match uu____4992 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5000) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5033 = is_mutual t'  in
                    if uu____5033
                    then true
                    else
                      (let uu____5035 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5035)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5051) -> is_mutual t'
                | uu____5056 -> false
              
              and exists_mutual uu___87_5057 =
                match uu___87_5057 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5076 =
                let uu____5077 = FStar_Syntax_Subst.compress dt1  in
                uu____5077.FStar_Syntax_Syntax.n  in
              match uu____5076 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5083) ->
                  let dbs1 =
                    let uu____5107 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5107  in
                  let dbs2 =
                    let uu____5145 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5145 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5163 =
                               let uu____5168 =
                                 let uu____5169 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5169]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5168
                                in
                             uu____5163 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5193 = is_mutual sort  in
                             if uu____5193
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
                           let uu____5205 =
                             let uu____5210 =
                               let uu____5211 =
                                 let uu____5218 =
                                   let uu____5219 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5219 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5218  in
                               [uu____5211]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5210
                              in
                           uu____5205 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5252 -> acc
  
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
              let uu____5301 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5323,bs,t,uu____5326,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5338 -> failwith "Impossible!"  in
              match uu____5301 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5361 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5361 t  in
                  let uu____5368 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5368 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5378 =
                           let uu____5379 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5379.FStar_Syntax_Syntax.n  in
                         match uu____5378 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5383) ->
                             ibs
                         | uu____5400 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5407 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5408 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5407
                           uu____5408
                          in
                       let ind1 =
                         let uu____5414 =
                           let uu____5419 =
                             FStar_List.map
                               (fun uu____5432  ->
                                  match uu____5432 with
                                  | (bv,aq) ->
                                      let uu____5443 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5443, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5419  in
                         uu____5414 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5449 =
                           let uu____5454 =
                             FStar_List.map
                               (fun uu____5467  ->
                                  match uu____5467 with
                                  | (bv,aq) ->
                                      let uu____5478 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5478, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5454  in
                         uu____5449 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5484 =
                           let uu____5489 =
                             let uu____5490 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5490]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5489
                            in
                         uu____5484 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5522,uu____5523,uu____5524,t_lid,uu____5526,uu____5527)
                                  -> t_lid = lid
                              | uu____5532 -> failwith "Impossible")
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
                         let uu___101_5542 = fml  in
                         let uu____5543 =
                           let uu____5544 =
                             let uu____5551 =
                               let uu____5552 =
                                 let uu____5563 =
                                   let uu____5572 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5572]  in
                                 [uu____5563]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5552
                                in
                             (fml, uu____5551)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5544  in
                         {
                           FStar_Syntax_Syntax.n = uu____5543;
                           FStar_Syntax_Syntax.pos =
                             (uu___101_5542.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___101_5542.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5617 =
                                  let uu____5622 =
                                    let uu____5623 =
                                      let uu____5630 =
                                        let uu____5631 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5631
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5630
                                       in
                                    [uu____5623]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5622
                                   in
                                uu____5617 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5672 =
                                  let uu____5677 =
                                    let uu____5678 =
                                      let uu____5685 =
                                        let uu____5686 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5686
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5685
                                       in
                                    [uu____5678]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5677
                                   in
                                uu____5672 FStar_Pervasives_Native.None
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
                     (lid,uu____5763,uu____5764,uu____5765,uu____5766,uu____5767)
                     -> lid
                 | uu____5776 -> failwith "Impossible!") tcs
             in
          let uu____5777 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5789,uu____5790,uu____5791,uu____5792) ->
                (lid, us)
            | uu____5801 -> failwith "Impossible!"  in
          match uu____5777 with
          | (lid,us) ->
              let uu____5810 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5810 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5837 =
                       let uu____5838 =
                         let uu____5845 = get_haseq_axiom_lid lid  in
                         (uu____5845, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5838  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5837;
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
          let uu____5898 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___88_5923  ->
                    match uu___88_5923 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5924;
                        FStar_Syntax_Syntax.sigrng = uu____5925;
                        FStar_Syntax_Syntax.sigquals = uu____5926;
                        FStar_Syntax_Syntax.sigmeta = uu____5927;
                        FStar_Syntax_Syntax.sigattrs = uu____5928;_} -> true
                    | uu____5949 -> false))
             in
          match uu____5898 with
          | (tys,datas) ->
              ((let uu____5971 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___89_5980  ->
                          match uu___89_5980 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5981;
                              FStar_Syntax_Syntax.sigrng = uu____5982;
                              FStar_Syntax_Syntax.sigquals = uu____5983;
                              FStar_Syntax_Syntax.sigmeta = uu____5984;
                              FStar_Syntax_Syntax.sigattrs = uu____5985;_} ->
                              false
                          | uu____6004 -> true))
                   in
                if uu____5971
                then
                  let uu____6005 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6005
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6013 =
                       let uu____6014 = FStar_List.hd tys  in
                       uu____6014.FStar_Syntax_Syntax.sigel  in
                     match uu____6013 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6017,uvs,uu____6019,uu____6020,uu____6021,uu____6022)
                         -> uvs
                     | uu____6031 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6035 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6061 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6061 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6099,bs,t,l1,l2) ->
                                      let uu____6112 =
                                        let uu____6129 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6130 =
                                          let uu____6131 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6131
                                            t
                                           in
                                        (lid, univs2, uu____6129, uu____6130,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6112
                                  | uu____6142 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___102_6143 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___102_6143.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___102_6143.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___102_6143.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___102_6143.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6153,t,lid_t,x,l) ->
                                      let uu____6162 =
                                        let uu____6177 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6177, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6162
                                  | uu____6180 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___103_6181 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___103_6181.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___103_6181.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___103_6181.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___103_6181.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6182 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6182, tys1, datas1))
                   in
                match uu____6035 with
                | (env1,tys1,datas1) ->
                    let uu____6208 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6247  ->
                             match uu____6247 with
                             | (env2,all_tcs,g) ->
                                 let uu____6287 = tc_tycon env2 tc  in
                                 (match uu____6287 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____6314 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____6314
                                        then
                                          let uu____6315 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____6315
                                        else ());
                                       (let uu____6317 =
                                          let uu____6318 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____6318
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____6317))))) tys1
                        (env1, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____6208 with
                     | (env2,tcs,g) ->
                         let uu____6364 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____6386  ->
                                  match uu____6386 with
                                  | (datas2,g1) ->
                                      let uu____6405 =
                                        let uu____6410 = tc_data env2 tcs  in
                                        uu____6410 se  in
                                      (match uu____6405 with
                                       | (data,g') ->
                                           let uu____6427 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____6427)))
                             datas1 ([], g)
                            in
                         (match uu____6364 with
                          | (datas2,g1) ->
                              let uu____6448 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____6466 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____6466, datas2))
                                 in
                              (match uu____6448 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____6498 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____6499 =
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
                                         uu____6498;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____6499
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____6525,uu____6526)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6546 =
                                                    let uu____6551 =
                                                      let uu____6552 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6553 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6552 uu____6553
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6551)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6546
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6554 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6554 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6570)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6599 ->
                                                             let uu____6600 =
                                                               let uu____6607
                                                                 =
                                                                 let uu____6608
                                                                   =
                                                                   let uu____6621
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6621)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6608
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6607
                                                                in
                                                             uu____6600
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
                                                       let uu____6643 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6643 with
                                                        | (uu____6648,inferred)
                                                            ->
                                                            let uu____6650 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6650
                                                             with
                                                             | (uu____6655,expected)
                                                                 ->
                                                                 let uu____6657
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6657
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6660 -> ()));
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
                          let uu____6752 =
                            let uu____6759 =
                              let uu____6760 =
                                let uu____6767 =
                                  let uu____6770 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6770  in
                                (uu____6767, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6760  in
                            FStar_Syntax_Syntax.mk uu____6759  in
                          uu____6752 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6799  ->
                                  match uu____6799 with
                                  | (x,imp) ->
                                      let uu____6810 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6810, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6812 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6812  in
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
                               let uu____6829 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6829
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6830 =
                               let uu____6833 =
                                 let uu____6836 =
                                   let uu____6841 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6842 =
                                     let uu____6843 =
                                       let uu____6850 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6850
                                        in
                                     [uu____6843]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6841
                                     uu____6842
                                    in
                                 uu____6836 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6833  in
                             FStar_Syntax_Util.refine x uu____6830  in
                           let uu____6871 =
                             let uu___104_6872 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___104_6872.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___104_6872.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6871)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6887 =
                          FStar_List.map
                            (fun uu____6909  ->
                               match uu____6909 with
                               | (x,uu____6921) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6887 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6966  ->
                                match uu____6966 with
                                | (x,uu____6978) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____6984 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____6984)
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
                               (let uu____6997 =
                                  let uu____6998 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____6998.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____6997)
                              in
                           let quals =
                             let uu____7002 =
                               FStar_List.filter
                                 (fun uu___90_7006  ->
                                    match uu___90_7006 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7007 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7002
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7034 =
                                 let uu____7035 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7035  in
                               FStar_Syntax_Syntax.mk_Total uu____7034  in
                             let uu____7036 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7036
                              in
                           let decl =
                             let uu____7040 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7040;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7042 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7042
                            then
                              let uu____7043 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7043
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
                                             fun uu____7094  ->
                                               match uu____7094 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7118 =
                                                       let uu____7121 =
                                                         let uu____7122 =
                                                           let uu____7129 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7129,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7122
                                                          in
                                                       pos uu____7121  in
                                                     (uu____7118, b)
                                                   else
                                                     (let uu____7135 =
                                                        let uu____7138 =
                                                          let uu____7139 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7139
                                                           in
                                                        pos uu____7138  in
                                                      (uu____7135, b))))
                                      in
                                   let pat_true =
                                     let uu____7157 =
                                       let uu____7160 =
                                         let uu____7161 =
                                           let uu____7174 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7174, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7161
                                          in
                                       pos uu____7160  in
                                     (uu____7157,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7208 =
                                       let uu____7211 =
                                         let uu____7212 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7212
                                          in
                                       pos uu____7211  in
                                     (uu____7208,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____7224 =
                                     let uu____7231 =
                                       let uu____7232 =
                                         let uu____7255 =
                                           let uu____7272 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7287 =
                                             let uu____7304 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7304]  in
                                           uu____7272 :: uu____7287  in
                                         (arg_exp, uu____7255)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7232
                                        in
                                     FStar_Syntax_Syntax.mk uu____7231  in
                                   uu____7224 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____7383 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7383
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
                                let uu____7397 =
                                  let uu____7402 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____7402  in
                                let uu____7403 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____7397
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____7403 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____7409 =
                                  let uu____7410 =
                                    let uu____7417 =
                                      let uu____7420 =
                                        let uu____7421 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____7421
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____7420]  in
                                    ((false, [lb]), uu____7417)  in
                                  FStar_Syntax_Syntax.Sig_let uu____7410  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7409;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____7433 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7433
                               then
                                 let uu____7434 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7434
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
                                fun uu____7486  ->
                                  match uu____7486 with
                                  | (a,uu____7492) ->
                                      let uu____7493 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7493 with
                                       | (field_name,uu____7499) ->
                                           let field_proj_tm =
                                             let uu____7501 =
                                               let uu____7502 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7502
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7501 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7523 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7561  ->
                                    match uu____7561 with
                                    | (x,uu____7569) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7571 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7571 with
                                         | (field_name,uu____7579) ->
                                             let t =
                                               let uu____7583 =
                                                 let uu____7584 =
                                                   let uu____7587 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7587
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7584
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7583
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____7592 =
                                                    let uu____7593 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7593.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7592)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7609 =
                                                   FStar_List.filter
                                                     (fun uu___91_7613  ->
                                                        match uu___91_7613
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7614 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7609
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___92_7627  ->
                                                         match uu___92_7627
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7628 ->
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
                                               let uu____7636 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____7636;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____7638 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7638
                                               then
                                                 let uu____7639 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7639
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
                                                           fun uu____7685  ->
                                                             match uu____7685
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
                                                                   let uu____7709
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7709,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7725
                                                                    =
                                                                    let uu____7728
                                                                    =
                                                                    let uu____7729
                                                                    =
                                                                    let uu____7736
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7736,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7729
                                                                     in
                                                                    pos
                                                                    uu____7728
                                                                     in
                                                                    (uu____7725,
                                                                    b))
                                                                   else
                                                                    (let uu____7742
                                                                    =
                                                                    let uu____7745
                                                                    =
                                                                    let uu____7746
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7746
                                                                     in
                                                                    pos
                                                                    uu____7745
                                                                     in
                                                                    (uu____7742,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7764 =
                                                     let uu____7767 =
                                                       let uu____7768 =
                                                         let uu____7781 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____7781,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7768
                                                        in
                                                     pos uu____7767  in
                                                   let uu____7790 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7764,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7790)
                                                    in
                                                 let body =
                                                   let uu____7806 =
                                                     let uu____7813 =
                                                       let uu____7814 =
                                                         let uu____7837 =
                                                           let uu____7854 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7854]  in
                                                         (arg_exp,
                                                           uu____7837)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7814
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7813
                                                      in
                                                   uu____7806
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____7922 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7922
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
                                                   let uu____7933 =
                                                     let uu____7938 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7938
                                                      in
                                                   let uu____7939 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7933;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7939;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____7945 =
                                                     let uu____7946 =
                                                       let uu____7953 =
                                                         let uu____7956 =
                                                           let uu____7957 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____7957
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____7956]  in
                                                       ((false, [lb]),
                                                         uu____7953)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7946
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7945;
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
                                                 (let uu____7969 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7969
                                                  then
                                                    let uu____7970 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7970
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7523 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8018) when
              let uu____8023 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8023 ->
              let uu____8024 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8024 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8046 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8046 with
                    | (formals,uu____8062) ->
                        let uu____8079 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8111 =
                                   let uu____8112 =
                                     let uu____8113 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8113  in
                                   FStar_Ident.lid_equals typ_lid uu____8112
                                    in
                                 if uu____8111
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8132,uvs',tps,typ0,uu____8136,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8153 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____8194 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____8194
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8079 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8219 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____8219 with
                              | (indices,uu____8235) ->
                                  let refine_domain =
                                    let uu____8253 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___93_8258  ->
                                              match uu___93_8258 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8259 -> true
                                              | uu____8268 -> false))
                                       in
                                    if uu____8253
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___94_8278 =
                                      match uu___94_8278 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8281,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8293 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____8294 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____8294 with
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
                                    let uu____8305 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8305 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8370  ->
                                               fun uu____8371  ->
                                                 match (uu____8370,
                                                         uu____8371)
                                                 with
                                                 | ((x,uu____8389),(x',uu____8391))
                                                     ->
                                                     let uu____8400 =
                                                       let uu____8407 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8407)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8400) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8412 -> []
  