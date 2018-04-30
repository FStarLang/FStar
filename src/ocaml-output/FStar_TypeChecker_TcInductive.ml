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
                                                            FStar_Syntax_Syntax.Delta_constant
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
                                                          (let uu___73_368 =
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
                                                               (uu___73_368.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___73_368.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___73_368.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___73_368.FStar_Syntax_Syntax.sigattrs)
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
                                                 (fun uu____591  ->
                                                    match uu____591 with
                                                    | (x,uu____603) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____607 =
                                            let uu____614 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____614, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____607
                                      | uu____621 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____662 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____662
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____469 with
                       | (env2,tps,u_tc) ->
                           let uu____687 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____701 =
                               let uu____702 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____702.FStar_Syntax_Syntax.n  in
                             match uu____701 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____735 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____735 with
                                  | (uu____768,bs') ->
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
                                                fun uu____825  ->
                                                  match uu____825 with
                                                  | (x,uu____831) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____832 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____832)
                             | uu____833 -> ([], t2)  in
                           (match uu____687 with
                            | (arguments,result) ->
                                ((let uu____867 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____867
                                  then
                                    let uu____868 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____869 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____870 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____868 uu____869 uu____870
                                  else ());
                                 (let uu____872 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____872 with
                                  | (arguments1,env',us) ->
                                      let uu____886 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____886 with
                                       | (result1,res_lcomp) ->
                                           ((let uu____898 =
                                               let uu____899 =
                                                 FStar_Syntax_Subst.compress
                                                   res_lcomp.FStar_Syntax_Syntax.res_typ
                                                  in
                                               uu____899.FStar_Syntax_Syntax.n
                                                in
                                             match uu____898 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____902 -> ()
                                             | ty ->
                                                 let uu____904 =
                                                   let uu____909 =
                                                     let uu____910 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____911 =
                                                       FStar_Syntax_Print.term_to_string
                                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____910 uu____911
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____909)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____904
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____912 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____912 with
                                             | (head1,uu____932) ->
                                                 let g_uvs =
                                                   let uu____954 =
                                                     let uu____955 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____955.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____954 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____959;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____960;_},tuvs)
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
                                                                  let uu____973
                                                                    =
                                                                    let uu____974
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____975
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
                                                                    uu____974
                                                                    uu____975
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g
                                                                    uu____973)
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
                                                   | uu____978 ->
                                                       let uu____979 =
                                                         let uu____984 =
                                                           let uu____985 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____986 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____985
                                                             uu____986
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____984)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____979
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____999  ->
                                                          fun u_x  ->
                                                            match uu____999
                                                            with
                                                            | (x,uu____1006)
                                                                ->
                                                                let uu____1007
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Rel.conj_guard
                                                                  g
                                                                  uu____1007)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1011 =
                                                     let uu____1018 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1050 
                                                               ->
                                                               match uu____1050
                                                               with
                                                               | (x,uu____1062)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1018 arguments1
                                                      in
                                                   let uu____1069 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1011 uu____1069
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___74_1074 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___74_1074.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___74_1074.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___74_1074.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___74_1074.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1077 -> failwith "impossible"
  
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
            let uu___75_1142 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___75_1142.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___75_1142.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___75_1142.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1152 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1152
           then
             let uu____1153 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1153
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1189  ->
                     match uu____1189 with
                     | (se,uu____1195) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1196,uu____1197,tps,k,uu____1200,uu____1201)
                              ->
                              let uu____1210 =
                                let uu____1211 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1211
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1210
                          | uu____1216 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1240,uu____1241,t,uu____1243,uu____1244,uu____1245)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1250 -> failwith "Impossible"))
              in
           let t =
             let uu____1254 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1254
              in
           (let uu____1262 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1262
            then
              let uu____1263 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1263
            else ());
           (let uu____1265 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1265 with
            | (uvs,t1) ->
                ((let uu____1285 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1285
                  then
                    let uu____1286 =
                      let uu____1287 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1287
                        (FStar_String.concat ", ")
                       in
                    let uu____1298 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1286 uu____1298
                  else ());
                 (let uu____1300 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1300 with
                  | (uvs1,t2) ->
                      let uu____1315 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1315 with
                       | (args,uu____1337) ->
                           let uu____1354 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1354 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1441  ->
                                       fun uu____1442  ->
                                         match (uu____1441, uu____1442) with
                                         | ((x,uu____1460),(se,uu____1462))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1472,tps,uu____1474,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1486 =
                                                    let uu____1499 =
                                                      let uu____1500 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1500.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1499 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1533 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1533
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1605
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1628 -> ([], ty)
                                                     in
                                                  (match uu____1486 with
                                                   | (tps1,t3) ->
                                                       let uu___76_1657 = se
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
                                                           (uu___76_1657.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___76_1657.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___76_1657.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___76_1657.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1662 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1668 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_17  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_17))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___64_1690  ->
                                                match uu___64_1690 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1696,uu____1697,uu____1698,uu____1699,uu____1700);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1701;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1702;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1703;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1704;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1717 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1738  ->
                                           fun d  ->
                                             match uu____1738 with
                                             | (t3,uu____1745) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1747,uu____1748,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1757 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1757
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___77_1758 = d
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
                                                          (uu___77_1758.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___77_1758.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___77_1758.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___77_1758.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1761 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1776 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1776
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1788 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1788
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1804 =
      let uu____1805 = FStar_Syntax_Subst.compress t  in
      uu____1805.FStar_Syntax_Syntax.n  in
    match uu____1804 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1824 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1829 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1882 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1951  ->
               match uu____1951 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1986 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1986  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1882
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2206 =
             let uu____2207 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2207
              in
           debug_log env uu____2206);
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
           (let uu____2210 =
              let uu____2211 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2211
               in
            debug_log env uu____2210);
           (let uu____2214 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2214) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2225 =
                  let uu____2226 = FStar_Syntax_Subst.compress btype1  in
                  uu____2226.FStar_Syntax_Syntax.n  in
                match uu____2225 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2251 = try_get_fv t  in
                    (match uu____2251 with
                     | (fv,us) ->
                         let uu____2258 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2258
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2268  ->
                                 match uu____2268 with
                                 | (t1,uu____2274) ->
                                     let uu____2275 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2275) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2317 =
                        let uu____2318 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____2318  in
                      if uu____2317
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2330  ->
                               match uu____2330 with
                               | (b,uu____2336) ->
                                   let uu____2337 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2337) sbs)
                           &&
                           ((let uu____2342 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2342 with
                             | (uu____2347,return_type) ->
                                 let uu____2349 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2349)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2370 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2372 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2375) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2402) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2428,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2486  ->
                          match uu____2486 with
                          | (p,uu____2498,t) ->
                              let bs =
                                let uu____2515 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2515
                                 in
                              let uu____2522 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2522 with
                               | (bs1,t1) ->
                                   let uu____2529 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2529)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2551,uu____2552)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2614 ->
                    ((let uu____2616 =
                        let uu____2617 =
                          let uu____2618 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2619 =
                            let uu____2620 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2620  in
                          Prims.strcat uu____2618 uu____2619  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2617
                         in
                      debug_log env uu____2616);
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
              (let uu____2638 =
                 let uu____2639 =
                   let uu____2640 =
                     let uu____2641 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2641  in
                   Prims.strcat ilid.FStar_Ident.str uu____2640  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2639
                  in
               debug_log env uu____2638);
              (let uu____2642 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2642 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2657 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2657
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2682 =
                            let uu____2683 =
                              let uu____2684 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2684
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2683
                             in
                          debug_log env uu____2682);
                         (let uu____2686 =
                            let uu____2687 = FStar_ST.op_Bang unfolded  in
                            let uu____2737 =
                              let uu____2744 =
                                let uu____2749 =
                                  let uu____2750 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2750  in
                                (ilid, uu____2749)  in
                              [uu____2744]  in
                            FStar_List.append uu____2687 uu____2737  in
                          FStar_ST.op_Colon_Equals unfolded uu____2686);
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
                  (let uu____2889 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2889 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2911 ->
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
                         (let uu____2914 =
                            let uu____2915 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2915
                             in
                          debug_log env uu____2914);
                         (let uu____2916 =
                            let uu____2917 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2917.FStar_Syntax_Syntax.n  in
                          match uu____2916 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2939 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2939 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____2988 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2988 dbs1
                                       in
                                    let c1 =
                                      let uu____2992 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2992 c
                                       in
                                    let uu____2995 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____2995 with
                                     | (args1,uu____3023) ->
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
                                           let uu____3095 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3095 c1
                                            in
                                         ((let uu____3103 =
                                             let uu____3104 =
                                               let uu____3105 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3106 =
                                                 let uu____3107 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3107
                                                  in
                                               Prims.strcat uu____3105
                                                 uu____3106
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3104
                                              in
                                           debug_log env uu____3103);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3136 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3138 =
                                  let uu____3139 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3139.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3138
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
                   (let uu____3201 = try_get_fv t1  in
                    match uu____3201 with
                    | (fv,uu____3207) ->
                        let uu____3208 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3208
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3229 =
                      let uu____3230 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3230
                       in
                    debug_log env uu____3229);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3232 =
                      FStar_List.fold_left
                        (fun uu____3249  ->
                           fun b  ->
                             match uu____3249 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3270 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3291 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3270, uu____3291))) (true, env)
                        sbs1
                       in
                    match uu____3232 with | (b,uu____3301) -> b))
              | uu____3302 ->
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
              let uu____3353 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3353 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3375 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3377 =
                      let uu____3378 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3378
                       in
                    debug_log env uu____3377);
                   (let uu____3379 =
                      let uu____3380 = FStar_Syntax_Subst.compress dt  in
                      uu____3380.FStar_Syntax_Syntax.n  in
                    match uu____3379 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3383 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3386) ->
                        let dbs1 =
                          let uu____3410 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3410  in
                        let dbs2 =
                          let uu____3448 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3448 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3453 =
                            let uu____3454 =
                              let uu____3455 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3455 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3454
                             in
                          debug_log env uu____3453);
                         (let uu____3460 =
                            FStar_List.fold_left
                              (fun uu____3477  ->
                                 fun b  ->
                                   match uu____3477 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3498 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3519 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3498, uu____3519)))
                              (true, env) dbs3
                             in
                          match uu____3460 with | (b,uu____3529) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3530,uu____3531) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3580 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3598 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3614,uu____3615,uu____3616) -> (lid, us, bs)
        | uu____3625 -> failwith "Impossible!"  in
      match uu____3598 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3635 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3635 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3658 =
                 let uu____3661 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3661  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3673 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3673
                      unfolded_inductives env2) uu____3658)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3703,uu____3704,t,uu____3706,uu____3707,uu____3708) -> t
    | uu____3713 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3733 =
         let uu____3734 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3734 haseq_suffix  in
       uu____3733 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3754 =
      let uu____3757 =
        let uu____3760 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3760]  in
      FStar_List.append lid.FStar_Ident.ns uu____3757  in
    FStar_Ident.lid_of_ids uu____3754
  
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
          let uu____3805 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3819,bs,t,uu____3822,uu____3823) -> (lid, bs, t)
            | uu____3832 -> failwith "Impossible!"  in
          match uu____3805 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3854 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3854 t  in
              let uu____3861 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3861 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3879 =
                       let uu____3880 = FStar_Syntax_Subst.compress t2  in
                       uu____3880.FStar_Syntax_Syntax.n  in
                     match uu____3879 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3884) -> ibs
                     | uu____3901 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3908 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3909 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3908 uu____3909
                      in
                   let ind1 =
                     let uu____3915 =
                       let uu____3920 =
                         FStar_List.map
                           (fun uu____3933  ->
                              match uu____3933 with
                              | (bv,aq) ->
                                  let uu____3944 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3944, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3920  in
                     uu____3915 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3950 =
                       let uu____3955 =
                         FStar_List.map
                           (fun uu____3968  ->
                              match uu____3968 with
                              | (bv,aq) ->
                                  let uu____3979 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3979, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3955  in
                     uu____3950 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____3985 =
                       let uu____3990 =
                         let uu____3991 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____3991]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____3990
                        in
                     uu____3985 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4030 =
                            let uu____4031 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4031  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4030) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4042 =
                              let uu____4045 =
                                let uu____4050 =
                                  let uu____4051 =
                                    let uu____4058 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4058  in
                                  [uu____4051]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4050
                                 in
                              uu____4045 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4042)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___78_4077 = fml  in
                     let uu____4078 =
                       let uu____4079 =
                         let uu____4086 =
                           let uu____4087 =
                             let uu____4098 =
                               let uu____4107 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4107]  in
                             [uu____4098]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4087  in
                         (fml, uu____4086)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4079  in
                     {
                       FStar_Syntax_Syntax.n = uu____4078;
                       FStar_Syntax_Syntax.pos =
                         (uu___78_4077.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___78_4077.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4152 =
                              let uu____4157 =
                                let uu____4158 =
                                  let uu____4165 =
                                    let uu____4166 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4166 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4165  in
                                [uu____4158]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4157
                               in
                            uu____4152 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4207 =
                              let uu____4212 =
                                let uu____4213 =
                                  let uu____4220 =
                                    let uu____4221 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4221 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4220  in
                                [uu____4213]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4212
                               in
                            uu____4207 FStar_Pervasives_Native.None
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
          let uu____4281 =
            let uu____4282 = FStar_Syntax_Subst.compress dt1  in
            uu____4282.FStar_Syntax_Syntax.n  in
          match uu____4281 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4286) ->
              let dbs1 =
                let uu____4310 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4310  in
              let dbs2 =
                let uu____4348 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4348 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4363 =
                           let uu____4368 =
                             let uu____4369 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4369]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4368
                            in
                         uu____4363 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4392 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4392 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4400 =
                       let uu____4405 =
                         let uu____4406 =
                           let uu____4413 =
                             let uu____4414 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4414
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4413  in
                         [uu____4406]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4405
                        in
                     uu____4400 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4447 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____4537,uu____4538,uu____4539,uu____4540,uu____4541)
                  -> lid
              | uu____4550 -> failwith "Impossible!"  in
            let uu____4551 = acc  in
            match uu____4551 with
            | (uu____4588,en,uu____4590,uu____4591) ->
                let uu____4612 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4612 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4649 = acc  in
                     (match uu____4649 with
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
                                     (uu____4723,uu____4724,uu____4725,t_lid,uu____4727,uu____4728)
                                     -> t_lid = lid
                                 | uu____4733 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4746 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4746)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4749 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4752 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4749, uu____4752)))
  
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
                (uu____4811,us,uu____4813,uu____4814,uu____4815,uu____4816)
                -> us
            | uu____4825 -> failwith "Impossible!"  in
          let uu____4826 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4826 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4851 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4851 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4929 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4929 with
                     | (phi1,uu____4937) ->
                         ((let uu____4939 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4939
                           then
                             let uu____4940 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4940
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4957  ->
                                    match uu____4957 with
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
                let uu____5025 =
                  let uu____5026 = FStar_Syntax_Subst.compress t  in
                  uu____5026.FStar_Syntax_Syntax.n  in
                match uu____5025 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5033) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5066 = is_mutual t'  in
                    if uu____5066
                    then true
                    else
                      (let uu____5068 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5068)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5084) -> is_mutual t'
                | uu____5089 -> false
              
              and exists_mutual uu___65_5090 =
                match uu___65_5090 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5109 =
                let uu____5110 = FStar_Syntax_Subst.compress dt1  in
                uu____5110.FStar_Syntax_Syntax.n  in
              match uu____5109 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5116) ->
                  let dbs1 =
                    let uu____5140 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5140  in
                  let dbs2 =
                    let uu____5178 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5178 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5196 =
                               let uu____5201 =
                                 let uu____5202 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5202]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5201
                                in
                             uu____5196 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5226 = is_mutual sort  in
                             if uu____5226
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
                           let uu____5238 =
                             let uu____5243 =
                               let uu____5244 =
                                 let uu____5251 =
                                   let uu____5252 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5252 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5251  in
                               [uu____5244]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5243
                              in
                           uu____5238 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5285 -> acc
  
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
              let uu____5334 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5356,bs,t,uu____5359,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5371 -> failwith "Impossible!"  in
              match uu____5334 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5394 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5394 t  in
                  let uu____5401 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5401 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5411 =
                           let uu____5412 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5412.FStar_Syntax_Syntax.n  in
                         match uu____5411 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5416) ->
                             ibs
                         | uu____5433 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5440 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5441 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5440
                           uu____5441
                          in
                       let ind1 =
                         let uu____5447 =
                           let uu____5452 =
                             FStar_List.map
                               (fun uu____5465  ->
                                  match uu____5465 with
                                  | (bv,aq) ->
                                      let uu____5476 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5476, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5452  in
                         uu____5447 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5482 =
                           let uu____5487 =
                             FStar_List.map
                               (fun uu____5500  ->
                                  match uu____5500 with
                                  | (bv,aq) ->
                                      let uu____5511 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5511, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5487  in
                         uu____5482 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5517 =
                           let uu____5522 =
                             let uu____5523 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5523]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5522
                            in
                         uu____5517 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5555,uu____5556,uu____5557,t_lid,uu____5559,uu____5560)
                                  -> t_lid = lid
                              | uu____5565 -> failwith "Impossible")
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
                         let uu___79_5575 = fml  in
                         let uu____5576 =
                           let uu____5577 =
                             let uu____5584 =
                               let uu____5585 =
                                 let uu____5596 =
                                   let uu____5605 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5605]  in
                                 [uu____5596]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5585
                                in
                             (fml, uu____5584)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5577  in
                         {
                           FStar_Syntax_Syntax.n = uu____5576;
                           FStar_Syntax_Syntax.pos =
                             (uu___79_5575.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___79_5575.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5650 =
                                  let uu____5655 =
                                    let uu____5656 =
                                      let uu____5663 =
                                        let uu____5664 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5664
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5663
                                       in
                                    [uu____5656]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5655
                                   in
                                uu____5650 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5705 =
                                  let uu____5710 =
                                    let uu____5711 =
                                      let uu____5718 =
                                        let uu____5719 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5719
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5718
                                       in
                                    [uu____5711]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5710
                                   in
                                uu____5705 FStar_Pervasives_Native.None
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
                     (lid,uu____5796,uu____5797,uu____5798,uu____5799,uu____5800)
                     -> lid
                 | uu____5809 -> failwith "Impossible!") tcs
             in
          let uu____5810 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5822,uu____5823,uu____5824,uu____5825) ->
                (lid, us)
            | uu____5834 -> failwith "Impossible!"  in
          match uu____5810 with
          | (lid,us) ->
              let uu____5843 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5843 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5870 =
                       let uu____5871 =
                         let uu____5878 = get_haseq_axiom_lid lid  in
                         (uu____5878, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5871  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5870;
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
          let uu____5931 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___66_5956  ->
                    match uu___66_5956 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5957;
                        FStar_Syntax_Syntax.sigrng = uu____5958;
                        FStar_Syntax_Syntax.sigquals = uu____5959;
                        FStar_Syntax_Syntax.sigmeta = uu____5960;
                        FStar_Syntax_Syntax.sigattrs = uu____5961;_} -> true
                    | uu____5982 -> false))
             in
          match uu____5931 with
          | (tys,datas) ->
              ((let uu____6004 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___67_6013  ->
                          match uu___67_6013 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6014;
                              FStar_Syntax_Syntax.sigrng = uu____6015;
                              FStar_Syntax_Syntax.sigquals = uu____6016;
                              FStar_Syntax_Syntax.sigmeta = uu____6017;
                              FStar_Syntax_Syntax.sigattrs = uu____6018;_} ->
                              false
                          | uu____6037 -> true))
                   in
                if uu____6004
                then
                  let uu____6038 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6038
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6047 =
                       let uu____6048 = FStar_List.hd tys  in
                       uu____6048.FStar_Syntax_Syntax.sigel  in
                     match uu____6047 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6051,uvs,uu____6053,uu____6054,uu____6055,uu____6056)
                         -> uvs
                     | uu____6065 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6069 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6096 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6096 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6134,bs,t,l1,l2) ->
                                      let uu____6147 =
                                        let uu____6164 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6165 =
                                          let uu____6166 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6166
                                            t
                                           in
                                        (lid, univs2, uu____6164, uu____6165,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6147
                                  | uu____6177 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___80_6178 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___80_6178.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___80_6178.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___80_6178.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___80_6178.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6188,t,lid_t,x,l) ->
                                      let uu____6197 =
                                        let uu____6212 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6212, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6197
                                  | uu____6215 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___81_6216 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___81_6216.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___81_6216.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___81_6216.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___81_6216.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6217 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6217, tys1, datas1))
                   in
                match uu____6069 with
                | (env1,tys1,datas1) ->
                    let uu____6243 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6282  ->
                             match uu____6282 with
                             | (env2,all_tcs,g) ->
                                 let uu____6322 = tc_tycon env2 tc  in
                                 (match uu____6322 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____6349 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____6349
                                        then
                                          let uu____6350 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____6350
                                        else ());
                                       (let uu____6352 =
                                          let uu____6353 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____6353
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____6352))))) tys1
                        (env1, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____6243 with
                     | (env2,tcs,g) ->
                         let uu____6399 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____6421  ->
                                  match uu____6421 with
                                  | (datas2,g1) ->
                                      let uu____6440 =
                                        let uu____6445 = tc_data env2 tcs  in
                                        uu____6445 se  in
                                      (match uu____6440 with
                                       | (data,g') ->
                                           let uu____6462 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____6462)))
                             datas1 ([], g)
                            in
                         (match uu____6399 with
                          | (datas2,g1) ->
                              let uu____6483 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____6502 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____6502, datas2))
                                 in
                              (match uu____6483 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____6534 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____6535 =
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
                                         uu____6534;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____6535
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____6561,uu____6562)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____6582 =
                                                    let uu____6587 =
                                                      let uu____6588 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____6589 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____6588 uu____6589
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____6587)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6582
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____6590 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____6590 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____6606)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____6633 ->
                                                             let uu____6634 =
                                                               let uu____6641
                                                                 =
                                                                 let uu____6642
                                                                   =
                                                                   let uu____6655
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____6655)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____6642
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____6641
                                                                in
                                                             uu____6634
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
                                                       let uu____6675 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____6675 with
                                                        | (uu____6680,inferred)
                                                            ->
                                                            let uu____6682 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____6682
                                                             with
                                                             | (uu____6687,expected)
                                                                 ->
                                                                 let uu____6689
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____6689
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____6692 -> ()));
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
                          let uu____6784 =
                            let uu____6791 =
                              let uu____6792 =
                                let uu____6799 =
                                  let uu____6802 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____6802  in
                                (uu____6799, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____6792  in
                            FStar_Syntax_Syntax.mk uu____6791  in
                          uu____6784 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6831  ->
                                  match uu____6831 with
                                  | (x,imp) ->
                                      let uu____6842 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6842, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6844 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6844  in
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
                               let uu____6861 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6861
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6862 =
                               let uu____6865 =
                                 let uu____6868 =
                                   let uu____6873 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6874 =
                                     let uu____6875 =
                                       let uu____6882 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6882
                                        in
                                     [uu____6875]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6873
                                     uu____6874
                                    in
                                 uu____6868 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6865  in
                             FStar_Syntax_Util.refine x uu____6862  in
                           let uu____6903 =
                             let uu___82_6904 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___82_6904.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___82_6904.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6903)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6919 =
                          FStar_List.map
                            (fun uu____6941  ->
                               match uu____6941 with
                               | (x,uu____6953) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6919 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6998  ->
                                match uu____6998 with
                                | (x,uu____7010) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7016 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7016)
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
                               (let uu____7029 =
                                  let uu____7030 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7030.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7029)
                              in
                           let quals =
                             let uu____7034 =
                               FStar_List.filter
                                 (fun uu___68_7038  ->
                                    match uu___68_7038 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7039 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7034
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7064 =
                                 let uu____7065 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7065  in
                               FStar_Syntax_Syntax.mk_Total uu____7064  in
                             let uu____7066 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7066
                              in
                           let decl =
                             let uu____7068 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7068;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7070 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7070
                            then
                              let uu____7071 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7071
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
                                             fun uu____7122  ->
                                               match uu____7122 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7146 =
                                                       let uu____7149 =
                                                         let uu____7150 =
                                                           let uu____7157 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7157,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7150
                                                          in
                                                       pos uu____7149  in
                                                     (uu____7146, b)
                                                   else
                                                     (let uu____7163 =
                                                        let uu____7166 =
                                                          let uu____7167 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7167
                                                           in
                                                        pos uu____7166  in
                                                      (uu____7163, b))))
                                      in
                                   let pat_true =
                                     let uu____7185 =
                                       let uu____7188 =
                                         let uu____7189 =
                                           let uu____7202 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7202, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7189
                                          in
                                       pos uu____7188  in
                                     (uu____7185,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7236 =
                                       let uu____7239 =
                                         let uu____7240 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7240
                                          in
                                       pos uu____7239  in
                                     (uu____7236,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____7252 =
                                     let uu____7259 =
                                       let uu____7260 =
                                         let uu____7283 =
                                           let uu____7300 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7315 =
                                             let uu____7332 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7332]  in
                                           uu____7300 :: uu____7315  in
                                         (arg_exp, uu____7283)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7260
                                        in
                                     FStar_Syntax_Syntax.mk uu____7259  in
                                   uu____7252 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____7411 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7411
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
                                let uu____7425 =
                                  let uu____7430 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____7430  in
                                let uu____7431 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____7425
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____7431 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____7437 =
                                  let uu____7438 =
                                    let uu____7445 =
                                      let uu____7448 =
                                        let uu____7449 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____7449
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____7448]  in
                                    ((false, [lb]), uu____7445)  in
                                  FStar_Syntax_Syntax.Sig_let uu____7438  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7437;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____7461 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7461
                               then
                                 let uu____7462 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7462
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
                                fun uu____7514  ->
                                  match uu____7514 with
                                  | (a,uu____7520) ->
                                      let uu____7521 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7521 with
                                       | (field_name,uu____7527) ->
                                           let field_proj_tm =
                                             let uu____7529 =
                                               let uu____7530 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7530
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7529 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7551 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7589  ->
                                    match uu____7589 with
                                    | (x,uu____7597) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7599 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7599 with
                                         | (field_name,uu____7607) ->
                                             let t =
                                               let uu____7611 =
                                                 let uu____7612 =
                                                   let uu____7615 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7615
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7612
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7611
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____7620 =
                                                    let uu____7621 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7621.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7620)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7637 =
                                                   FStar_List.filter
                                                     (fun uu___69_7641  ->
                                                        match uu___69_7641
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7642 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7637
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___70_7655  ->
                                                         match uu___70_7655
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7656 ->
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
                                               let uu____7668 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____7668;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____7670 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7670
                                               then
                                                 let uu____7671 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7671
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
                                                           fun uu____7717  ->
                                                             match uu____7717
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
                                                                   let uu____7741
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7741,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7757
                                                                    =
                                                                    let uu____7760
                                                                    =
                                                                    let uu____7761
                                                                    =
                                                                    let uu____7768
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7768,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7761
                                                                     in
                                                                    pos
                                                                    uu____7760
                                                                     in
                                                                    (uu____7757,
                                                                    b))
                                                                   else
                                                                    (let uu____7774
                                                                    =
                                                                    let uu____7777
                                                                    =
                                                                    let uu____7778
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7778
                                                                     in
                                                                    pos
                                                                    uu____7777
                                                                     in
                                                                    (uu____7774,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7796 =
                                                     let uu____7799 =
                                                       let uu____7800 =
                                                         let uu____7813 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____7813,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7800
                                                        in
                                                     pos uu____7799  in
                                                   let uu____7822 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7796,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7822)
                                                    in
                                                 let body =
                                                   let uu____7838 =
                                                     let uu____7845 =
                                                       let uu____7846 =
                                                         let uu____7869 =
                                                           let uu____7886 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7886]  in
                                                         (arg_exp,
                                                           uu____7869)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7846
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7845
                                                      in
                                                   uu____7838
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____7954 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7954
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
                                                   let uu____7965 =
                                                     let uu____7970 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7970
                                                      in
                                                   let uu____7971 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7965;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7971;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____7977 =
                                                     let uu____7978 =
                                                       let uu____7985 =
                                                         let uu____7988 =
                                                           let uu____7989 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____7989
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____7988]  in
                                                       ((false, [lb]),
                                                         uu____7985)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7978
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7977;
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
                                                 (let uu____8001 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8001
                                                  then
                                                    let uu____8002 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8002
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7551 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8050) when
              let uu____8055 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8055 ->
              let uu____8056 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8056 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8078 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8078 with
                    | (formals,uu____8094) ->
                        let uu____8111 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8143 =
                                   let uu____8144 =
                                     let uu____8145 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8145  in
                                   FStar_Ident.lid_equals typ_lid uu____8144
                                    in
                                 if uu____8143
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8164,uvs',tps,typ0,uu____8168,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8185 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____8226 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____8226
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8111 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8251 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____8251 with
                              | (indices,uu____8267) ->
                                  let refine_domain =
                                    let uu____8285 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___71_8290  ->
                                              match uu___71_8290 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8291 -> true
                                              | uu____8300 -> false))
                                       in
                                    if uu____8285
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___72_8310 =
                                      match uu___72_8310 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8313,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8325 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____8326 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____8326 with
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
                                    let uu____8337 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8337 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8402  ->
                                               fun uu____8403  ->
                                                 match (uu____8402,
                                                         uu____8403)
                                                 with
                                                 | ((x,uu____8421),(x',uu____8423))
                                                     ->
                                                     let uu____8432 =
                                                       let uu____8439 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8439)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8432) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8444 -> []
  