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
          let uu____37 = FStar_Syntax_Subst.open_term tps k  in
          (match uu____37 with
           | (tps1,k1) ->
               let uu____52 = FStar_TypeChecker_TcTerm.tc_binders env tps1
                  in
               (match uu____52 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1
                       in
                    let uu____74 = FStar_Syntax_Util.arrow_formals k2  in
                    (match uu____74 with
                     | (indices,t) ->
                         let uu____113 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____113 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____134 =
                                let uu____139 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____139 with
                                | (t1,uu____151,g) ->
                                    let uu____153 =
                                      let uu____154 =
                                        let uu____155 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____155
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____154
                                       in
                                    (t1, uu____153)
                                 in
                              (match uu____134 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____169 =
                                       FStar_Syntax_Syntax.mk_Total t1  in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____169
                                      in
                                   let uu____172 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____172 with
                                    | (t_type,u) ->
                                        ((let uu____188 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____188);
                                         (let t_tc =
                                            let uu____192 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____192
                                             in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3
                                             in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          let uu____202 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              (uvs, t_tc)
                                             in
                                          (uu____202,
                                            (let uu___71_206 = s  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, uvs, tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___71_206.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___71_206.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___71_206.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___71_206.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____211 -> failwith "impossible"
  
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
            let uu____268 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____307  ->
                     match uu____307 with
                     | (se1,u_tc) ->
                         let uu____322 =
                           let uu____323 =
                             let uu____324 =
                               FStar_Syntax_Util.lid_of_sigelt se1  in
                             FStar_Util.must uu____324  in
                           FStar_Ident.lid_equals tc_lid uu____323  in
                         if uu____322
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____343,uu____344,tps,uu____346,uu____347,uu____348)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____387  ->
                                          match uu____387 with
                                          | (x,uu____399) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____403 =
                                  let uu____410 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____410, tps2, u_tc)  in
                                FStar_Pervasives_Native.Some uu____403
                            | uu____417 -> failwith "Impossible")
                         else FStar_Pervasives_Native.None)
                 in
              match tps_u_opt with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None  ->
                  let uu____458 =
                    FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid
                     in
                  if uu____458
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedDataConstructor,
                        "Unexpected data constructor")
                      se.FStar_Syntax_Syntax.sigrng
               in
            (match uu____268 with
             | (env1,tps,u_tc) ->
                 let uu____489 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t
                      in
                   let uu____503 =
                     let uu____504 = FStar_Syntax_Subst.compress t1  in
                     uu____504.FStar_Syntax_Syntax.n  in
                   match uu____503 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____537 = FStar_Util.first_N ntps bs  in
                       (match uu____537 with
                        | (uu____570,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____621  ->
                                        match uu____621 with
                                        | (x,uu____627) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____628 =
                              FStar_Syntax_Subst.subst subst1 t2  in
                            FStar_Syntax_Util.arrow_formals uu____628)
                   | uu____629 -> ([], t1)  in
                 (match uu____489 with
                  | (arguments,result) ->
                      ((let uu____663 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____663
                        then
                          let uu____664 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____665 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____666 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____664
                            uu____665 uu____666
                        else ());
                       (let uu____668 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____668 with
                        | (arguments1,env',us) ->
                            let uu____682 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____682 with
                             | (result1,res_lcomp) ->
                                 ((let uu____694 =
                                     let uu____695 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                        in
                                     uu____695.FStar_Syntax_Syntax.n  in
                                   match uu____694 with
                                   | FStar_Syntax_Syntax.Tm_type uu____698 ->
                                       ()
                                   | ty ->
                                       let uu____700 =
                                         let uu____705 =
                                           let uu____706 =
                                             FStar_Syntax_Print.term_to_string
                                               result1
                                              in
                                           let uu____707 =
                                             FStar_Syntax_Print.term_to_string
                                               res_lcomp.FStar_Syntax_Syntax.res_typ
                                              in
                                           FStar_Util.format2
                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                             uu____706 uu____707
                                            in
                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                           uu____705)
                                          in
                                       FStar_Errors.raise_error uu____700
                                         se.FStar_Syntax_Syntax.sigrng);
                                  (let uu____708 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____708 with
                                   | (head1,uu____728) ->
                                       ((let uu____750 =
                                           let uu____751 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____751.FStar_Syntax_Syntax.n
                                            in
                                         match uu____750 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             ({
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_fvar
                                                  fv;
                                                FStar_Syntax_Syntax.pos =
                                                  uu____755;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____756;_},uu____757)
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____763 ->
                                             let uu____764 =
                                               let uu____769 =
                                                 let uu____770 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     tc_lid
                                                    in
                                                 let uu____771 =
                                                   FStar_Syntax_Print.term_to_string
                                                     head1
                                                    in
                                                 FStar_Util.format2
                                                   "Expected a constructor of type %s; got %s"
                                                   uu____770 uu____771
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                 uu____769)
                                                in
                                             FStar_Errors.raise_error
                                               uu____764
                                               se.FStar_Syntax_Syntax.sigrng);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____784  ->
                                                  fun u_x  ->
                                                    match uu____784 with
                                                    | (x,uu____791) ->
                                                        let uu____792 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____792)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____796 =
                                             let uu____803 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____833  ->
                                                       match uu____833 with
                                                       | (x,uu____845) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____803
                                               arguments1
                                              in
                                           let uu____854 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1
                                              in
                                           FStar_Syntax_Util.arrow uu____796
                                             uu____854
                                            in
                                         ((let uu___72_858 = se  in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___72_858.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___72_858.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___72_858.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___72_858.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____865 -> failwith "impossible"
  
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
            let uu___73_922 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___73_922.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___73_922.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___73_922.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____932 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____932
           then
             let uu____933 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____933
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____961  ->
                     match uu____961 with
                     | (se,uu____967) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____968,uu____969,tps,k,uu____972,uu____973)
                              ->
                              let uu____982 =
                                let uu____983 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____983
                                 in
                              FStar_Syntax_Syntax.null_binder uu____982
                          | uu____990 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1006,uu____1007,t,uu____1009,uu____1010,uu____1011)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1016 -> failwith "Impossible"))
              in
           let t =
             let uu____1020 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1020
              in
           (let uu____1024 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1024
            then
              let uu____1025 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1025
            else ());
           (let uu____1027 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1027 with
            | (uvs,t1) ->
                ((let uu____1043 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1043
                  then
                    let uu____1044 =
                      let uu____1045 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1045
                        (FStar_String.concat ", ")
                       in
                    let uu____1056 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1044 uu____1056
                  else ());
                 (let uu____1058 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1058 with
                  | (uvs1,t2) ->
                      let uu____1073 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1073 with
                       | (args,uu____1095) ->
                           let uu____1112 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1112 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1195  ->
                                       fun uu____1196  ->
                                         match (uu____1195, uu____1196) with
                                         | ((x,uu____1214),(se,uu____1216))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1226,tps,uu____1228,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1240 =
                                                    let uu____1253 =
                                                      let uu____1254 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1254.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1253 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1287 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1287
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1359
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1382 -> ([], ty)
                                                     in
                                                  (match uu____1240 with
                                                   | (tps1,t3) ->
                                                       let uu___74_1411 = se
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
                                                           (uu___74_1411.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___74_1411.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___74_1411.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___74_1411.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1424 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1430 ->
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
                                             (fun uu___62_1472  ->
                                                match uu___62_1472 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1480,uu____1481,uu____1482,uu____1483,uu____1484);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1485;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1486;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1487;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1488;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1503 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1526  ->
                                           fun d  ->
                                             match uu____1526 with
                                             | (t3,uu____1533) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1535,uu____1536,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1545 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1545
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___75_1546 = d
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
                                                          (uu___75_1546.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___75_1546.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___75_1546.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___75_1546.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1549 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit) =
  fun env  ->
    fun s  ->
      let uu____1560 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1560
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1568 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1568
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1582 =
      let uu____1583 = FStar_Syntax_Subst.compress t  in
      uu____1583.FStar_Syntax_Syntax.n  in
    match uu____1582 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1604 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1609 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1654 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1719  ->
               match uu____1719 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1754 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1754  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1654
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1926 =
             let uu____1927 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____1927
              in
           debug_log env uu____1926);
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
           (let uu____1930 =
              let uu____1931 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1931
               in
            debug_log env uu____1930);
           (let uu____1934 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____1934) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1945 =
                  let uu____1946 = FStar_Syntax_Subst.compress btype1  in
                  uu____1946.FStar_Syntax_Syntax.n  in
                match uu____1945 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1971 = try_get_fv t  in
                    (match uu____1971 with
                     | (fv,us) ->
                         let uu____1978 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____1978
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1988  ->
                                 match uu____1988 with
                                 | (t1,uu____1994) ->
                                     let uu____1995 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____1995) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2037 =
                        let uu____2038 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____2038  in
                      if uu____2037
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2050  ->
                               match uu____2050 with
                               | (b,uu____2056) ->
                                   let uu____2057 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2057) sbs)
                           &&
                           ((let uu____2062 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2062 with
                             | (uu____2067,return_type) ->
                                 let uu____2069 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2069)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2090 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2092 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2095) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2122) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2148,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2206  ->
                          match uu____2206 with
                          | (p,uu____2218,t) ->
                              let bs =
                                let uu____2231 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2231
                                 in
                              let uu____2234 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2234 with
                               | (bs1,t1) ->
                                   let uu____2241 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2241)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2263,uu____2264)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2326 ->
                    ((let uu____2328 =
                        let uu____2329 =
                          let uu____2330 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2331 =
                            let uu____2332 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2332  in
                          Prims.strcat uu____2330 uu____2331  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2329
                         in
                      debug_log env uu____2328);
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
              (let uu____2350 =
                 let uu____2351 =
                   let uu____2352 =
                     let uu____2353 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2353  in
                   Prims.strcat ilid.FStar_Ident.str uu____2352  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2351
                  in
               debug_log env uu____2350);
              (let uu____2354 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2354 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2369 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2369
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2394 =
                            let uu____2395 =
                              let uu____2396 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2396
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2395
                             in
                          debug_log env uu____2394);
                         (let uu____2398 =
                            let uu____2399 = FStar_ST.op_Bang unfolded  in
                            let uu____2445 =
                              let uu____2452 =
                                let uu____2465 =
                                  let uu____2474 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____2474  in
                                (ilid, uu____2465)  in
                              [uu____2452]  in
                            FStar_List.append uu____2399 uu____2445  in
                          FStar_ST.op_Colon_Equals unfolded uu____2398);
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
                  (let uu____2633 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____2633 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2655 ->
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
                         (let uu____2658 =
                            let uu____2659 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2659
                             in
                          debug_log env uu____2658);
                         (let uu____2660 =
                            let uu____2661 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____2661.FStar_Syntax_Syntax.n  in
                          match uu____2660 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2683 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____2683 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____2732 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2732 dbs1
                                       in
                                    let c1 =
                                      let uu____2736 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2736 c
                                       in
                                    let uu____2739 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____2739 with
                                     | (args1,uu____2767) ->
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
                                           let uu____2839 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2839 c1
                                            in
                                         ((let uu____2847 =
                                             let uu____2848 =
                                               let uu____2849 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____2850 =
                                                 let uu____2851 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____2851
                                                  in
                                               Prims.strcat uu____2849
                                                 uu____2850
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2848
                                              in
                                           debug_log env uu____2847);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2872 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2874 =
                                  let uu____2875 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____2875.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____2874
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
                   (let uu____2937 = try_get_fv t1  in
                    match uu____2937 with
                    | (fv,uu____2943) ->
                        let uu____2944 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____2944
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____2965 =
                      let uu____2966 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2966
                       in
                    debug_log env uu____2965);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____2968 =
                      FStar_List.fold_left
                        (fun uu____2985  ->
                           fun b  ->
                             match uu____2985 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3006 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3027 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3006, uu____3027))) (true, env)
                        sbs1
                       in
                    match uu____2968 with | (b,uu____3037) -> b))
              | uu____3038 ->
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
              let uu____3077 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3077 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3099 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3101 =
                      let uu____3102 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3102
                       in
                    debug_log env uu____3101);
                   (let uu____3103 =
                      let uu____3104 = FStar_Syntax_Subst.compress dt  in
                      uu____3104.FStar_Syntax_Syntax.n  in
                    match uu____3103 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3107 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3110) ->
                        let dbs1 =
                          let uu____3134 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3134  in
                        let dbs2 =
                          let uu____3172 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3172 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3177 =
                            let uu____3178 =
                              let uu____3179 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3179 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3178
                             in
                          debug_log env uu____3177);
                         (let uu____3184 =
                            FStar_List.fold_left
                              (fun uu____3201  ->
                                 fun b  ->
                                   match uu____3201 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3222 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3243 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3222, uu____3243)))
                              (true, env) dbs3
                             in
                          match uu____3184 with | (b,uu____3253) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3254,uu____3255) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3304 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3330 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3346,uu____3347,uu____3348) -> (lid, us, bs)
        | uu____3357 -> failwith "Impossible!"  in
      match uu____3330 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3367 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____3367 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____3390 =
                 let uu____3393 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____3393  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3405 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3405
                      unfolded_inductives env2) uu____3390)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3433,uu____3434,t,uu____3436,uu____3437,uu____3438) -> t
    | uu____3443 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____3461 =
         let uu____3462 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____3462 haseq_suffix  in
       uu____3461 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____3480 =
      let uu____3483 =
        let uu____3486 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____3486]  in
      FStar_List.append lid.FStar_Ident.ns uu____3483  in
    FStar_Ident.lid_of_ids uu____3480
  
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
          let uu____3523 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____3537,bs,t,uu____3540,uu____3541) -> (lid, bs, t)
            | uu____3550 -> failwith "Impossible!"  in
          match uu____3523 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____3572 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____3572 t  in
              let uu____3579 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____3579 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____3603 =
                       let uu____3604 = FStar_Syntax_Subst.compress t2  in
                       uu____3604.FStar_Syntax_Syntax.n  in
                     match uu____3603 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3614) -> ibs
                     | uu____3631 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____3638 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____3639 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____3638 uu____3639
                      in
                   let ind1 =
                     let uu____3645 =
                       let uu____3646 =
                         FStar_List.map
                           (fun uu____3659  ->
                              match uu____3659 with
                              | (bv,aq) ->
                                  let uu____3670 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3670, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____3646  in
                     uu____3645 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____3676 =
                       let uu____3677 =
                         FStar_List.map
                           (fun uu____3690  ->
                              match uu____3690 with
                              | (bv,aq) ->
                                  let uu____3701 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____3701, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3677  in
                     uu____3676 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____3707 =
                       let uu____3708 =
                         let uu____3709 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____3709]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____3708
                        in
                     uu____3707 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____3730 =
                            let uu____3731 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____3731  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____3730) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____3742 =
                              let uu____3743 =
                                let uu____3744 =
                                  let uu____3745 =
                                    let uu____3746 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____3746  in
                                  [uu____3745]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____3744
                                 in
                              uu____3743 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____3742)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___76_3753 = fml  in
                     let uu____3754 =
                       let uu____3755 =
                         let uu____3762 =
                           let uu____3763 =
                             let uu____3774 =
                               let uu____3777 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____3777]  in
                             [uu____3774]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____3763  in
                         (fml, uu____3762)  in
                       FStar_Syntax_Syntax.Tm_meta uu____3755  in
                     {
                       FStar_Syntax_Syntax.n = uu____3754;
                       FStar_Syntax_Syntax.pos =
                         (uu___76_3753.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___76_3753.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____3790 =
                              let uu____3791 =
                                let uu____3792 =
                                  let uu____3793 =
                                    let uu____3794 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____3794 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____3793  in
                                [uu____3792]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____3791
                               in
                            uu____3790 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____3819 =
                              let uu____3820 =
                                let uu____3821 =
                                  let uu____3822 =
                                    let uu____3823 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____3823 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____3822  in
                                [uu____3821]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____3820
                               in
                            uu____3819 FStar_Pervasives_Native.None
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
          let uu____3859 =
            let uu____3860 = FStar_Syntax_Subst.compress dt1  in
            uu____3860.FStar_Syntax_Syntax.n  in
          match uu____3859 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3864) ->
              let dbs1 =
                let uu____3888 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____3888  in
              let dbs2 =
                let uu____3926 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____3926 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3941 =
                           let uu____3942 =
                             let uu____3943 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____3943]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3942
                            in
                         uu____3941 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____3948 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____3948 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3956 =
                       let uu____3957 =
                         let uu____3958 =
                           let uu____3959 =
                             let uu____3960 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3960
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____3959  in
                         [uu____3958]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3957
                        in
                     uu____3956 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3977 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____4049,uu____4050,uu____4051,uu____4052,uu____4053)
                  -> lid
              | uu____4062 -> failwith "Impossible!"  in
            let uu____4063 = acc  in
            match uu____4063 with
            | (uu____4096,en,uu____4098,uu____4099) ->
                let uu____4112 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____4112 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4149 = acc  in
                     (match uu____4149 with
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
                                     (uu____4211,uu____4212,uu____4213,t_lid,uu____4215,uu____4216)
                                     -> t_lid = lid
                                 | uu____4221 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4228 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4228)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____4229 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____4232 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____4229, uu____4232)))
  
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
                (uu____4283,us,uu____4285,uu____4286,uu____4287,uu____4288)
                -> us
            | uu____4297 -> failwith "Impossible!"  in
          let uu____4298 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____4298 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____4323 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____4323 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____4381 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____4381 with
                     | (phi1,uu____4389) ->
                         ((let uu____4391 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____4391
                           then
                             let uu____4392 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____4392
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____4408  ->
                                    match uu____4408 with
                                    | (lid,fml) ->
                                        FStar_List.append l
                                          [{
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_assume
                                                  (lid, us1, fml));
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
                let uu____4461 =
                  let uu____4462 = FStar_Syntax_Subst.compress t  in
                  uu____4462.FStar_Syntax_Syntax.n  in
                match uu____4461 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4469) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4502 = is_mutual t'  in
                    if uu____4502
                    then true
                    else
                      (let uu____4504 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____4504)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4520) -> is_mutual t'
                | uu____4525 -> false
              
              and exists_mutual uu___63_4526 =
                match uu___63_4526 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____4545 =
                let uu____4546 = FStar_Syntax_Subst.compress dt1  in
                uu____4546.FStar_Syntax_Syntax.n  in
              match uu____4545 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4552) ->
                  let dbs1 =
                    let uu____4576 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____4576  in
                  let dbs2 =
                    let uu____4614 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____4614 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____4632 =
                               let uu____4633 =
                                 let uu____4634 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____4634]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4633
                                in
                             uu____4632 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____4638 = is_mutual sort  in
                             if uu____4638
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
                           let uu____4648 =
                             let uu____4649 =
                               let uu____4650 =
                                 let uu____4651 =
                                   let uu____4652 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4652 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____4651  in
                               [uu____4650]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4649
                              in
                           uu____4648 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4669 -> acc
  
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
              let uu____4706 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4728,bs,t,uu____4731,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4743 -> failwith "Impossible!"  in
              match uu____4706 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____4766 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____4766 t  in
                  let uu____4773 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____4773 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4789 =
                           let uu____4790 = FStar_Syntax_Subst.compress t2
                              in
                           uu____4790.FStar_Syntax_Syntax.n  in
                         match uu____4789 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4800) ->
                             ibs
                         | uu____4817 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____4824 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____4825 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4824
                           uu____4825
                          in
                       let ind1 =
                         let uu____4831 =
                           let uu____4832 =
                             FStar_List.map
                               (fun uu____4845  ->
                                  match uu____4845 with
                                  | (bv,aq) ->
                                      let uu____4856 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____4856, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4832  in
                         uu____4831 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____4862 =
                           let uu____4863 =
                             FStar_List.map
                               (fun uu____4876  ->
                                  match uu____4876 with
                                  | (bv,aq) ->
                                      let uu____4887 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____4887, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4863  in
                         uu____4862 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____4893 =
                           let uu____4894 =
                             let uu____4895 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____4895]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4894
                            in
                         uu____4893 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4909,uu____4910,uu____4911,t_lid,uu____4913,uu____4914)
                                  -> t_lid = lid
                              | uu____4919 -> failwith "Impossible")
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
                         let uu___77_4925 = fml  in
                         let uu____4926 =
                           let uu____4927 =
                             let uu____4934 =
                               let uu____4935 =
                                 let uu____4946 =
                                   let uu____4949 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____4949]  in
                                 [uu____4946]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____4935
                                in
                             (fml, uu____4934)  in
                           FStar_Syntax_Syntax.Tm_meta uu____4927  in
                         {
                           FStar_Syntax_Syntax.n = uu____4926;
                           FStar_Syntax_Syntax.pos =
                             (uu___77_4925.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___77_4925.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4962 =
                                  let uu____4963 =
                                    let uu____4964 =
                                      let uu____4965 =
                                        let uu____4966 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4966
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____4965
                                       in
                                    [uu____4964]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4963
                                   in
                                uu____4962 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4991 =
                                  let uu____4992 =
                                    let uu____4993 =
                                      let uu____4994 =
                                        let uu____4995 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4995
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____4994
                                       in
                                    [uu____4993]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4992
                                   in
                                uu____4991 FStar_Pervasives_Native.None
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
                     (lid,uu____5048,uu____5049,uu____5050,uu____5051,uu____5052)
                     -> lid
                 | uu____5061 -> failwith "Impossible!") tcs
             in
          let uu____5062 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____5074,uu____5075,uu____5076,uu____5077) ->
                (lid, us)
            | uu____5086 -> failwith "Impossible!"  in
          match uu____5062 with
          | (lid,us) ->
              let uu____5095 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5095 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____5118 =
                       let uu____5119 =
                         let uu____5126 = get_haseq_axiom_lid lid  in
                         (uu____5126, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____5119  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5118;
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
          let uu____5173 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___64_5198  ->
                    match uu___64_5198 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5199;
                        FStar_Syntax_Syntax.sigrng = uu____5200;
                        FStar_Syntax_Syntax.sigquals = uu____5201;
                        FStar_Syntax_Syntax.sigmeta = uu____5202;
                        FStar_Syntax_Syntax.sigattrs = uu____5203;_} -> true
                    | uu____5224 -> false))
             in
          match uu____5173 with
          | (tys,datas) ->
              ((let uu____5246 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___65_5255  ->
                          match uu___65_5255 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5256;
                              FStar_Syntax_Syntax.sigrng = uu____5257;
                              FStar_Syntax_Syntax.sigquals = uu____5258;
                              FStar_Syntax_Syntax.sigmeta = uu____5259;
                              FStar_Syntax_Syntax.sigattrs = uu____5260;_} ->
                              false
                          | uu____5279 -> true))
                   in
                if uu____5246
                then
                  let uu____5280 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____5280
                else ());
               (let env0 = env  in
                let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____5289 =
                       let uu____5290 = FStar_List.hd tys  in
                       uu____5290.FStar_Syntax_Syntax.sigel  in
                     match uu____5289 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____5293,uvs,uu____5295,uu____5296,uu____5297,uu____5298)
                         -> uvs
                     | uu____5307 -> failwith "Impossible, can't happen!")
                   in
                let uu____5310 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (tys, datas)
                  else
                    (let uu____5332 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____5332 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____5368,bs,t,l1,l2) ->
                                      let uu____5381 =
                                        let uu____5398 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____5399 =
                                          let uu____5400 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____5400
                                            t
                                           in
                                        (lid, univs2, uu____5398, uu____5399,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____5381
                                  | uu____5413 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___78_5414 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___78_5414.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___78_5414.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___78_5414.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___78_5414.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____5424,t,lid_t,x,l) ->
                                      let uu____5433 =
                                        let uu____5448 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____5448, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____5433
                                  | uu____5453 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___79_5454 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___79_5454.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___79_5454.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___79_5454.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___79_5454.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         (tys1, datas1))
                   in
                match uu____5310 with
                | (tys1,datas1) ->
                    let uu____5479 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____5518  ->
                             match uu____5518 with
                             | (env1,all_tcs,g) ->
                                 let uu____5558 = tc_tycon env1 tc  in
                                 (match uu____5558 with
                                  | (env2,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____5585 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Low
                                           in
                                        if uu____5585
                                        then
                                          let uu____5586 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____5586
                                        else ());
                                       (let uu____5588 =
                                          let uu____5589 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____5589
                                           in
                                        (env2, ((tc1, tc_u) :: all_tcs),
                                          uu____5588))))) tys1
                        (env, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____5479 with
                     | (env1,tcs,g) ->
                         let uu____5635 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____5657  ->
                                  match uu____5657 with
                                  | (datas2,g1) ->
                                      let uu____5676 =
                                        let uu____5681 = tc_data env1 tcs  in
                                        uu____5681 se  in
                                      (match uu____5676 with
                                       | (data,g') ->
                                           let uu____5696 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____5696)))
                             datas1 ([], g)
                            in
                         (match uu____5635 with
                          | (datas2,g1) ->
                              let uu____5717 =
                                generalize_and_inst_within env0 g1 tcs datas2
                                 in
                              (match uu____5717 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____5747 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____5748 =
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
                                         uu____5747;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____5748
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____5774,uu____5775)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____5791 =
                                                    let uu____5796 =
                                                      let uu____5797 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____5798 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____5797 uu____5798
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____5796)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5791
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____5799 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____5799 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____5815)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____5836 ->
                                                             let uu____5837 =
                                                               let uu____5840
                                                                 =
                                                                 let uu____5841
                                                                   =
                                                                   let uu____5854
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____5854)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____5841
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____5840
                                                                in
                                                             uu____5837
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
                                                       let uu____5860 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____5860 with
                                                        | (uu____5865,inferred)
                                                            ->
                                                            let uu____5867 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____5867
                                                             with
                                                             | (uu____5872,expected)
                                                                 ->
                                                                 let uu____5874
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____5874
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____5877 -> ()));
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
                          let uu____5945 =
                            let uu____5948 =
                              let uu____5949 =
                                let uu____5956 =
                                  let uu____5957 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____5957  in
                                (uu____5956, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____5949  in
                            FStar_Syntax_Syntax.mk uu____5948  in
                          uu____5945 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____5998  ->
                                  match uu____5998 with
                                  | (x,imp) ->
                                      let uu____6009 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____6009, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____6011 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____6011  in
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
                               let uu____6020 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____6020
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____6021 =
                               let uu____6022 =
                                 let uu____6023 =
                                   let uu____6024 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____6025 =
                                     let uu____6026 =
                                       let uu____6027 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____6027
                                        in
                                     [uu____6026]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____6024
                                     uu____6025
                                    in
                                 uu____6023 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____6022  in
                             FStar_Syntax_Util.refine x uu____6021  in
                           let uu____6030 =
                             let uu___80_6031 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___80_6031.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___80_6031.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____6030)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____6046 =
                          FStar_List.map
                            (fun uu____6068  ->
                               match uu____6068 with
                               | (x,uu____6080) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____6046 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6129  ->
                                match uu____6129 with
                                | (x,uu____6141) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____6147 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____6147)
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
                               (let uu____6160 =
                                  let uu____6161 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____6161.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____6160)
                              in
                           let quals =
                             let uu____6165 =
                               FStar_List.filter
                                 (fun uu___66_6169  ->
                                    match uu___66_6169 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____6170 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____6165
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____6191 =
                                 let uu____6192 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____6192  in
                               FStar_Syntax_Syntax.mk_Total uu____6191  in
                             let uu____6193 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____6193
                              in
                           let decl =
                             let uu____6195 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____6195;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____6197 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____6197
                            then
                              let uu____6198 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____6198
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
                                             fun uu____6251  ->
                                               match uu____6251 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____6275 =
                                                       let uu____6278 =
                                                         let uu____6279 =
                                                           let uu____6286 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____6286,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____6279
                                                          in
                                                       pos uu____6278  in
                                                     (uu____6275, b)
                                                   else
                                                     (let uu____6290 =
                                                        let uu____6293 =
                                                          let uu____6294 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____6294
                                                           in
                                                        pos uu____6293  in
                                                      (uu____6290, b))))
                                      in
                                   let pat_true =
                                     let uu____6312 =
                                       let uu____6315 =
                                         let uu____6316 =
                                           let uu____6329 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____6329, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____6316
                                          in
                                       pos uu____6315  in
                                     (uu____6312,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____6363 =
                                       let uu____6366 =
                                         let uu____6367 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____6367
                                          in
                                       pos uu____6366  in
                                     (uu____6363,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____6379 =
                                     let uu____6382 =
                                       let uu____6383 =
                                         let uu____6406 =
                                           let uu____6409 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____6410 =
                                             let uu____6413 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____6413]  in
                                           uu____6409 :: uu____6410  in
                                         (arg_exp, uu____6406)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____6383
                                        in
                                     FStar_Syntax_Syntax.mk uu____6382  in
                                   uu____6379 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____6420 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____6420
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
                                let uu____6428 =
                                  let uu____6433 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____6433  in
                                let uu____6434 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____6428
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____6434 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____6440 =
                                  let uu____6441 =
                                    let uu____6448 =
                                      let uu____6451 =
                                        let uu____6452 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____6452
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____6451]  in
                                    ((false, [lb]), uu____6448)  in
                                  FStar_Syntax_Syntax.Sig_let uu____6441  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____6440;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____6470 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____6470
                               then
                                 let uu____6471 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____6471
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
                                fun uu____6513  ->
                                  match uu____6513 with
                                  | (a,uu____6519) ->
                                      let uu____6520 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____6520 with
                                       | (field_name,uu____6526) ->
                                           let field_proj_tm =
                                             let uu____6528 =
                                               let uu____6529 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____6529
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____6528 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____6546 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____6578  ->
                                    match uu____6578 with
                                    | (x,uu____6586) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____6588 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____6588 with
                                         | (field_name,uu____6596) ->
                                             let t =
                                               let uu____6598 =
                                                 let uu____6599 =
                                                   let uu____6602 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____6602
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____6599
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____6598
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____6605 =
                                                    let uu____6606 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____6606.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____6605)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____6620 =
                                                   FStar_List.filter
                                                     (fun uu___67_6624  ->
                                                        match uu___67_6624
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____6625 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____6620
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___68_6638  ->
                                                         match uu___68_6638
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____6639 ->
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
                                               let uu____6657 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____6657;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____6659 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____6659
                                               then
                                                 let uu____6660 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____6660
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
                                                           fun uu____6708  ->
                                                             match uu____6708
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
                                                                   let uu____6732
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____6732,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____6748
                                                                    =
                                                                    let uu____6751
                                                                    =
                                                                    let uu____6752
                                                                    =
                                                                    let uu____6759
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____6759,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____6752
                                                                     in
                                                                    pos
                                                                    uu____6751
                                                                     in
                                                                    (uu____6748,
                                                                    b))
                                                                   else
                                                                    (let uu____6763
                                                                    =
                                                                    let uu____6766
                                                                    =
                                                                    let uu____6767
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____6767
                                                                     in
                                                                    pos
                                                                    uu____6766
                                                                     in
                                                                    (uu____6763,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____6783 =
                                                     let uu____6786 =
                                                       let uu____6787 =
                                                         let uu____6800 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____6800,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____6787
                                                        in
                                                     pos uu____6786  in
                                                   let uu____6809 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____6783,
                                                     FStar_Pervasives_Native.None,
                                                     uu____6809)
                                                    in
                                                 let body =
                                                   let uu____6821 =
                                                     let uu____6824 =
                                                       let uu____6825 =
                                                         let uu____6848 =
                                                           let uu____6851 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____6851]  in
                                                         (arg_exp,
                                                           uu____6848)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____6825
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6824
                                                      in
                                                   uu____6821
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____6859 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____6859
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
                                                   let uu____6866 =
                                                     let uu____6871 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____6871
                                                      in
                                                   let uu____6872 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____6866;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____6872;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____6878 =
                                                     let uu____6879 =
                                                       let uu____6886 =
                                                         let uu____6889 =
                                                           let uu____6890 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____6890
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____6889]  in
                                                       ((false, [lb]),
                                                         uu____6886)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____6879
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____6878;
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
                                                 (let uu____6908 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____6908
                                                  then
                                                    let uu____6909 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____6909
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____6546 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____6949) when
              let uu____6954 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____6954 ->
              let uu____6955 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____6955 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____6977 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____6977 with
                    | (formals,uu____6993) ->
                        let uu____7010 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____7042 =
                                   let uu____7043 =
                                     let uu____7044 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____7044  in
                                   FStar_Ident.lid_equals typ_lid uu____7043
                                    in
                                 if uu____7042
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____7063,uvs',tps,typ0,uu____7067,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____7086 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____7127 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____7127
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____7010 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____7160 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____7160 with
                              | (indices,uu____7176) ->
                                  let refine_domain =
                                    let uu____7194 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___69_7199  ->
                                              match uu___69_7199 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____7200 -> true
                                              | uu____7209 -> false))
                                       in
                                    if uu____7194
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___70_7217 =
                                      match uu___70_7217 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____7220,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____7232 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____7233 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____7233 with
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
                                    let uu____7244 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____7244 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____7309  ->
                                               fun uu____7310  ->
                                                 match (uu____7309,
                                                         uu____7310)
                                                 with
                                                 | ((x,uu____7328),(x',uu____7330))
                                                     ->
                                                     let uu____7339 =
                                                       let uu____7346 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____7346)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____7339) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____7347 -> []
  