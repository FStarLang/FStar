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
                                            (let uu___61_206 = s  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, uvs, tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___61_206.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___61_206.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___61_206.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___61_206.FStar_Syntax_Syntax.sigattrs)
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
                                         ((let uu___62_858 = se  in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___62_858.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___62_858.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___62_858.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___62_858.FStar_Syntax_Syntax.sigattrs)
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
            let uu___63_922 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___63_922.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___63_922.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___63_922.FStar_TypeChecker_Env.implicits)
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
                                                       let uu___64_1411 = se
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
                                                           (uu___64_1411.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___64_1411.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___64_1411.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___64_1411.FStar_Syntax_Syntax.sigattrs)
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
                                             (fun uu___57_1472  ->
                                                match uu___57_1472 with
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
                                                      let uu___65_1546 = d
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
                                                          (uu___65_1546.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___65_1546.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___65_1546.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___65_1546.FStar_Syntax_Syntax.sigattrs)
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
          let uu____3462 =
            let uu____3463 = FStar_Syntax_Subst.compress dt1  in
            uu____3463.FStar_Syntax_Syntax.n  in
          match uu____3462 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3467) ->
              let dbs1 =
                let uu____3491 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____3491  in
              let dbs2 =
                let uu____3529 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____3529 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3544 =
                           let uu____3545 =
                             let uu____3546 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____3546]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3545
                            in
                         uu____3544 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____3551 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____3551 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3559 =
                       let uu____3560 =
                         let uu____3561 =
                           let uu____3562 =
                             let uu____3563 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3563
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____3562  in
                         [uu____3561]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3560
                        in
                     uu____3559 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3580 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____3652,uu____3653,uu____3654,uu____3655,uu____3656)
                  -> lid
              | uu____3665 -> failwith "Impossible!"  in
            let uu____3666 = acc  in
            match uu____3666 with
            | (uu____3699,en,uu____3701,uu____3702) ->
                let uu____3715 =
                  FStar_TypeChecker_Util.get_optimized_haseq_axiom en ty
                    usubst us
                   in
                (match uu____3715 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____3752 = acc  in
                     (match uu____3752 with
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
                                     (uu____3814,uu____3815,uu____3816,t_lid,uu____3818,uu____3819)
                                     -> t_lid = lid
                                 | uu____3824 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____3831 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____3831)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____3832 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____3835 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____3832, uu____3835)))
  
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
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          fun tc_assume  ->
            let us =
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____3918,us,uu____3920,uu____3921,uu____3922,uu____3923)
                  -> us
              | uu____3932 -> failwith "Impossible!"  in
            let uu____3933 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____3933 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____3958 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____3958 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____4016 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____4016 with
                       | (phi1,uu____4024) ->
                           ((let uu____4026 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____4026
                             then
                               let uu____4027 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4027
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____4044  ->
                                      match uu____4044 with
                                      | (lid,fml) ->
                                          let se =
                                            tc_assume env2 lid fml []
                                              FStar_Range.dummyRange
                                             in
                                          FStar_List.append l [se]) [] axioms
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
                let uu____4096 =
                  let uu____4097 = FStar_Syntax_Subst.compress t  in
                  uu____4097.FStar_Syntax_Syntax.n  in
                match uu____4096 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4104) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4137 = is_mutual t'  in
                    if uu____4137
                    then true
                    else
                      (let uu____4139 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____4139)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4155) -> is_mutual t'
                | uu____4160 -> false
              
              and exists_mutual uu___58_4161 =
                match uu___58_4161 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____4180 =
                let uu____4181 = FStar_Syntax_Subst.compress dt1  in
                uu____4181.FStar_Syntax_Syntax.n  in
              match uu____4180 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4187) ->
                  let dbs1 =
                    let uu____4211 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____4211  in
                  let dbs2 =
                    let uu____4249 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____4249 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____4267 =
                               let uu____4268 =
                                 let uu____4269 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____4269]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4268
                                in
                             uu____4267 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____4273 = is_mutual sort  in
                             if uu____4273
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
                           let uu____4283 =
                             let uu____4284 =
                               let uu____4285 =
                                 let uu____4286 =
                                   let uu____4287 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4287 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____4286  in
                               [uu____4285]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4284
                              in
                           uu____4283 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4304 -> acc
  
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
              let uu____4341 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4363,bs,t,uu____4366,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4378 -> failwith "Impossible!"  in
              match uu____4341 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____4401 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____4401 t  in
                  let uu____4408 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____4408 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4424 =
                           let uu____4425 = FStar_Syntax_Subst.compress t2
                              in
                           uu____4425.FStar_Syntax_Syntax.n  in
                         match uu____4424 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4435) ->
                             ibs
                         | uu____4452 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____4459 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____4460 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4459
                           uu____4460
                          in
                       let ind1 =
                         let uu____4466 =
                           let uu____4467 =
                             FStar_List.map
                               (fun uu____4480  ->
                                  match uu____4480 with
                                  | (bv,aq) ->
                                      let uu____4491 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____4491, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4467  in
                         uu____4466 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____4497 =
                           let uu____4498 =
                             FStar_List.map
                               (fun uu____4511  ->
                                  match uu____4511 with
                                  | (bv,aq) ->
                                      let uu____4522 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____4522, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4498  in
                         uu____4497 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____4528 =
                           let uu____4529 =
                             let uu____4530 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____4530]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4529
                            in
                         uu____4528 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4544,uu____4545,uu____4546,t_lid,uu____4548,uu____4549)
                                  -> t_lid = lid
                              | uu____4554 -> failwith "Impossible")
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
                         let uu___66_4560 = fml  in
                         let uu____4561 =
                           let uu____4562 =
                             let uu____4569 =
                               let uu____4570 =
                                 let uu____4581 =
                                   let uu____4584 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____4584]  in
                                 [uu____4581]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____4570
                                in
                             (fml, uu____4569)  in
                           FStar_Syntax_Syntax.Tm_meta uu____4562  in
                         {
                           FStar_Syntax_Syntax.n = uu____4561;
                           FStar_Syntax_Syntax.pos =
                             (uu___66_4560.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___66_4560.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4597 =
                                  let uu____4598 =
                                    let uu____4599 =
                                      let uu____4600 =
                                        let uu____4601 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4601
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____4600
                                       in
                                    [uu____4599]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4598
                                   in
                                uu____4597 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4626 =
                                  let uu____4627 =
                                    let uu____4628 =
                                      let uu____4629 =
                                        let uu____4630 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4630
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____4629
                                       in
                                    [uu____4628]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4627
                                   in
                                uu____4626 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2
                          in
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
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          fun tc_assume  ->
            let mutuals =
              FStar_List.map
                (fun ty  ->
                   match ty.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (lid,uu____4715,uu____4716,uu____4717,uu____4718,uu____4719)
                       -> lid
                   | uu____4728 -> failwith "Impossible!") tcs
               in
            let uu____4729 =
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____4741,uu____4742,uu____4743,uu____4744) ->
                  (lid, us)
              | uu____4753 -> failwith "Impossible!"  in
            match uu____4729 with
            | (lid,us) ->
                let uu____4762 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____4762 with
                 | (usubst,us1) ->
                     let fml =
                       FStar_List.fold_left
                         (unoptimized_haseq_ty datas mutuals usubst us1)
                         FStar_Syntax_Util.t_true tcs
                        in
                     let env =
                       FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
                     ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                        "haseq";
                      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                        env sig_bndle;
                      (let env1 =
                         FStar_TypeChecker_Env.push_univ_vars env us1  in
                       let se =
                         let uu____4789 =
                           let uu____4790 =
                             let uu____4793 =
                               let uu____4796 =
                                 FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")
                                  in
                               [uu____4796]  in
                             FStar_List.append lid.FStar_Ident.ns uu____4793
                              in
                           FStar_Ident.lid_of_ids uu____4790  in
                         tc_assume env1 uu____4789 fml []
                           FStar_Range.dummyRange
                          in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
  
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
          let uu____4842 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___59_4867  ->
                    match uu___59_4867 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____4868;
                        FStar_Syntax_Syntax.sigrng = uu____4869;
                        FStar_Syntax_Syntax.sigquals = uu____4870;
                        FStar_Syntax_Syntax.sigmeta = uu____4871;
                        FStar_Syntax_Syntax.sigattrs = uu____4872;_} -> true
                    | uu____4893 -> false))
             in
          match uu____4842 with
          | (tys,datas) ->
              ((let uu____4915 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___60_4924  ->
                          match uu___60_4924 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____4925;
                              FStar_Syntax_Syntax.sigrng = uu____4926;
                              FStar_Syntax_Syntax.sigquals = uu____4927;
                              FStar_Syntax_Syntax.sigmeta = uu____4928;
                              FStar_Syntax_Syntax.sigattrs = uu____4929;_} ->
                              false
                          | uu____4948 -> true))
                   in
                if uu____4915
                then
                  let uu____4949 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____4949
                else ());
               (let env0 = env  in
                let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____4958 =
                       let uu____4959 = FStar_List.hd tys  in
                       uu____4959.FStar_Syntax_Syntax.sigel  in
                     match uu____4958 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____4962,uvs,uu____4964,uu____4965,uu____4966,uu____4967)
                         -> uvs
                     | uu____4976 -> failwith "Impossible, can't happen!")
                   in
                let uu____4979 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (tys, datas)
                  else
                    (let uu____5001 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____5001 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____5037,bs,t,l1,l2) ->
                                      let uu____5050 =
                                        let uu____5067 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____5068 =
                                          let uu____5069 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____5069
                                            t
                                           in
                                        (lid, univs2, uu____5067, uu____5068,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____5050
                                  | uu____5082 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___67_5083 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___67_5083.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___67_5083.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___67_5083.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___67_5083.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____5093,t,lid_t,x,l) ->
                                      let uu____5102 =
                                        let uu____5117 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____5117, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____5102
                                  | uu____5122 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___68_5123 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___68_5123.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___68_5123.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___68_5123.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___68_5123.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         (tys1, datas1))
                   in
                match uu____4979 with
                | (tys1,datas1) ->
                    let uu____5148 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____5187  ->
                             match uu____5187 with
                             | (env1,all_tcs,g) ->
                                 let uu____5227 = tc_tycon env1 tc  in
                                 (match uu____5227 with
                                  | (env2,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____5254 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Low
                                           in
                                        if uu____5254
                                        then
                                          let uu____5255 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____5255
                                        else ());
                                       (let uu____5257 =
                                          let uu____5258 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Rel.conj_guard g
                                            uu____5258
                                           in
                                        (env2, ((tc1, tc_u) :: all_tcs),
                                          uu____5257))))) tys1
                        (env, [], FStar_TypeChecker_Rel.trivial_guard)
                       in
                    (match uu____5148 with
                     | (env1,tcs,g) ->
                         let uu____5304 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____5326  ->
                                  match uu____5326 with
                                  | (datas2,g1) ->
                                      let uu____5345 =
                                        let uu____5350 = tc_data env1 tcs  in
                                        uu____5350 se  in
                                      (match uu____5345 with
                                       | (data,g') ->
                                           let uu____5365 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____5365)))
                             datas1 ([], g)
                            in
                         (match uu____5304 with
                          | (datas2,g1) ->
                              let uu____5386 =
                                generalize_and_inst_within env0 g1 tcs datas2
                                 in
                              (match uu____5386 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____5416 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____5417 =
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
                                         uu____5416;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____5417
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____5443,uu____5444)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____5460 =
                                                    let uu____5465 =
                                                      let uu____5466 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____5467 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____5466 uu____5467
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____5465)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5460
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____5468 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____5468 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____5484)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____5505 ->
                                                             let uu____5506 =
                                                               let uu____5509
                                                                 =
                                                                 let uu____5510
                                                                   =
                                                                   let uu____5523
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____5523)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____5510
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____5509
                                                                in
                                                             uu____5506
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
                                                       let uu____5529 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____5529 with
                                                        | (uu____5534,inferred)
                                                            ->
                                                            let uu____5536 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____5536
                                                             with
                                                             | (uu____5541,expected)
                                                                 ->
                                                                 let uu____5543
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____5543
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____5546 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))
  