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
          let uu____40 = FStar_Syntax_Subst.open_term tps k  in
          (match uu____40 with
           | (tps1,k1) ->
               let uu____55 = FStar_TypeChecker_TcTerm.tc_binders env tps1
                  in
               (match uu____55 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1
                       in
                    let uu____77 = FStar_Syntax_Util.arrow_formals k2  in
                    (match uu____77 with
                     | (indices,t) ->
                         let uu____116 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____116 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____137 =
                                let uu____142 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____142 with
                                | (t1,uu____154,g) ->
                                    let uu____156 =
                                      let uu____157 =
                                        let uu____158 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____158
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____157
                                       in
                                    (t1, uu____156)
                                 in
                              (match uu____137 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____172 =
                                       FStar_Syntax_Syntax.mk_Total t1  in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____172
                                      in
                                   let uu____175 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____175 with
                                    | (t_type,u) ->
                                        ((let uu____191 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____191);
                                         (let t_tc =
                                            let uu____195 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____195
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
                                          let uu____205 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (uu____205,
                                            (let uu___58_211 = s  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___58_211.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___58_211.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___58_211.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___58_211.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____218 -> failwith "impossible"
  
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
            let uu____275 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____314  ->
                     match uu____314 with
                     | (se1,u_tc) ->
                         let uu____329 =
                           let uu____330 =
                             let uu____331 =
                               FStar_Syntax_Util.lid_of_sigelt se1  in
                             FStar_Util.must uu____331  in
                           FStar_Ident.lid_equals tc_lid uu____330  in
                         if uu____329
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____350,uu____351,tps,uu____353,uu____354,uu____355)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____394  ->
                                          match uu____394 with
                                          | (x,uu____406) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____410 =
                                  let uu____417 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____417, tps2, u_tc)  in
                                FStar_Pervasives_Native.Some uu____410
                            | uu____424 -> failwith "Impossible")
                         else FStar_Pervasives_Native.None)
                 in
              match tps_u_opt with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedDataConstructor,
                        "Unexpected data constructor")
                      se.FStar_Syntax_Syntax.sigrng
               in
            (match uu____275 with
             | (env1,tps,u_tc) ->
                 let uu____495 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t
                      in
                   let uu____509 =
                     let uu____510 = FStar_Syntax_Subst.compress t1  in
                     uu____510.FStar_Syntax_Syntax.n  in
                   match uu____509 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____543 = FStar_Util.first_N ntps bs  in
                       (match uu____543 with
                        | (uu____576,bs') ->
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
                                      fun uu____627  ->
                                        match uu____627 with
                                        | (x,uu____633) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____634 =
                              FStar_Syntax_Subst.subst subst1 t2  in
                            FStar_Syntax_Util.arrow_formals uu____634)
                   | uu____635 -> ([], t1)  in
                 (match uu____495 with
                  | (arguments,result) ->
                      ((let uu____669 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____669
                        then
                          let uu____670 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____671 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____672 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____670
                            uu____671 uu____672
                        else ());
                       (let uu____674 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____674 with
                        | (arguments1,env',us) ->
                            let uu____688 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____688 with
                             | (result1,res_lcomp) ->
                                 ((let uu____700 =
                                     let uu____701 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                        in
                                     uu____701.FStar_Syntax_Syntax.n  in
                                   match uu____700 with
                                   | FStar_Syntax_Syntax.Tm_type uu____704 ->
                                       ()
                                   | ty ->
                                       let uu____706 =
                                         let uu____711 =
                                           let uu____712 =
                                             FStar_Syntax_Print.term_to_string
                                               result1
                                              in
                                           let uu____713 =
                                             FStar_Syntax_Print.term_to_string
                                               res_lcomp.FStar_Syntax_Syntax.res_typ
                                              in
                                           FStar_Util.format2
                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                             uu____712 uu____713
                                            in
                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                           uu____711)
                                          in
                                       FStar_Errors.raise_error uu____706
                                         se.FStar_Syntax_Syntax.sigrng);
                                  (let uu____714 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____714 with
                                   | (head1,uu____734) ->
                                       ((let uu____756 =
                                           let uu____757 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____757.FStar_Syntax_Syntax.n
                                            in
                                         match uu____756 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____761 ->
                                             let uu____762 =
                                               let uu____767 =
                                                 let uu____768 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     tc_lid
                                                    in
                                                 let uu____769 =
                                                   FStar_Syntax_Print.term_to_string
                                                     head1
                                                    in
                                                 FStar_Util.format2
                                                   "Expected a constructor of type %s; got %s"
                                                   uu____768 uu____769
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                 uu____767)
                                                in
                                             FStar_Errors.raise_error
                                               uu____762
                                               se.FStar_Syntax_Syntax.sigrng);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____782  ->
                                                  fun u_x  ->
                                                    match uu____782 with
                                                    | (x,uu____789) ->
                                                        let uu____790 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____790)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____794 =
                                             let uu____801 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____831  ->
                                                       match uu____831 with
                                                       | (x,uu____843) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____801
                                               arguments1
                                              in
                                           let uu____852 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1
                                              in
                                           FStar_Syntax_Util.arrow uu____794
                                             uu____852
                                            in
                                         ((let uu___59_856 = se  in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___59_856.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___59_856.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___59_856.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___59_856.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____863 -> failwith "impossible"
  
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
            let uu___60_920 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___60_920.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___60_920.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___60_920.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____930 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____930
           then
             let uu____931 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____931
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____959  ->
                     match uu____959 with
                     | (se,uu____965) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____966,uu____967,tps,k,uu____970,uu____971)
                              ->
                              let uu____980 =
                                let uu____981 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____981
                                 in
                              FStar_Syntax_Syntax.null_binder uu____980
                          | uu____988 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1004,uu____1005,t,uu____1007,uu____1008,uu____1009)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1014 -> failwith "Impossible"))
              in
           let t =
             let uu____1018 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1018
              in
           (let uu____1022 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1022
            then
              let uu____1023 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1023
            else ());
           (let uu____1025 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1025 with
            | (uvs,t1) ->
                ((let uu____1041 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1041
                  then
                    let uu____1042 =
                      let uu____1043 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1043
                        (FStar_String.concat ", ")
                       in
                    let uu____1054 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1042 uu____1054
                  else ());
                 (let uu____1056 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1056 with
                  | (uvs1,t2) ->
                      let uu____1071 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1071 with
                       | (args,uu____1093) ->
                           let uu____1110 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1110 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1193  ->
                                       fun uu____1194  ->
                                         match (uu____1193, uu____1194) with
                                         | ((x,uu____1212),(se,uu____1214))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1224,tps,uu____1226,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1238 =
                                                    let uu____1251 =
                                                      let uu____1252 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1252.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1251 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1285 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1285
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1357
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1380 -> ([], ty)
                                                     in
                                                  (match uu____1238 with
                                                   | (tps1,t3) ->
                                                       let uu___61_1409 = se
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
                                                           (uu___61_1409.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___61_1409.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___61_1409.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___61_1409.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1422 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1428 ->
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
                                             (fun uu___54_1470  ->
                                                match uu___54_1470 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1478,uu____1479,uu____1480,uu____1481,uu____1482);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1483;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1484;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1485;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1486;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1501 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1524  ->
                                           fun d  ->
                                             match uu____1524 with
                                             | (t3,uu____1531) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1533,uu____1534,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1543 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1543
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___62_1544 = d
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
                                                          (uu___62_1544.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___62_1544.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___62_1544.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___62_1544.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1547 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit) =
  fun env  ->
    fun s  ->
      let uu____1558 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1558
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1566 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1566
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1580 =
      let uu____1581 = FStar_Syntax_Subst.compress t  in
      uu____1581.FStar_Syntax_Syntax.n  in
    match uu____1580 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1602 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1607 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1704 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____1821  ->
               match uu____1821 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1856 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____1856  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1704
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2158 =
             let uu____2159 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2159
              in
           debug_log env uu____2158);
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
           (let uu____2162 =
              let uu____2163 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2163
               in
            debug_log env uu____2162);
           (let uu____2166 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2166) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2176 =
                  let uu____2177 = FStar_Syntax_Subst.compress btype1  in
                  uu____2177.FStar_Syntax_Syntax.n  in
                match uu____2176 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2202 = try_get_fv t  in
                    (match uu____2202 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2218  ->
                                 match uu____2218 with
                                 | (t1,uu____2224) ->
                                     let uu____2225 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2225) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2319 =
                        let uu____2320 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____2320  in
                      if uu____2319
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2332  ->
                               match uu____2332 with
                               | (b,uu____2338) ->
                                   let uu____2339 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2339) sbs)
                           &&
                           ((let uu____2344 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2344 with
                             | (uu____2349,return_type) ->
                                 let uu____2351 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2351)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2424 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2426 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2429) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2508) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2586,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2644  ->
                          match uu____2644 with
                          | (p,uu____2656,t) ->
                              let bs =
                                let uu____2669 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2669
                                 in
                              let uu____2672 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2672 with
                               | (bs1,t1) ->
                                   let uu____2679 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2679)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2753,uu____2754)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2868 ->
                    ((let uu____2870 =
                        let uu____2871 =
                          let uu____2872 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2873 =
                            let uu____2874 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2874  in
                          Prims.strcat uu____2872 uu____2873  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2871
                         in
                      debug_log env uu____2870);
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
              (let uu____2918 =
                 let uu____2919 =
                   let uu____2920 =
                     let uu____2921 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2921  in
                   Prims.strcat ilid.FStar_Ident.str uu____2920  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2919
                  in
               debug_log env uu____2918);
              (let uu____2922 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2922 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2937 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2937
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____3014 =
                            let uu____3015 =
                              let uu____3016 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____3016
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____3015
                             in
                          debug_log env uu____3014);
                         (let uu____3018 =
                            let uu____3019 = FStar_ST.op_Bang unfolded  in
                            let uu____3117 =
                              let uu____3124 =
                                let uu____3137 =
                                  let uu____3146 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3146  in
                                (ilid, uu____3137)  in
                              [uu____3124]  in
                            FStar_List.append uu____3019 uu____3117  in
                          FStar_ST.op_Colon_Equals unfolded uu____3018);
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
                  (let uu____3435 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3435 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3457 ->
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
                         (let uu____3460 =
                            let uu____3461 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3461
                             in
                          debug_log env uu____3460);
                         (let uu____3462 =
                            let uu____3463 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3463.FStar_Syntax_Syntax.n  in
                          match uu____3462 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3485 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3485 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3534 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3534 dbs1
                                       in
                                    let c1 =
                                      let uu____3538 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3538 c
                                       in
                                    let uu____3541 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3541 with
                                     | (args1,uu____3569) ->
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
                                           let uu____3641 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3641 c1
                                            in
                                         ((let uu____3649 =
                                             let uu____3650 =
                                               let uu____3651 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3652 =
                                                 let uu____3653 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3653
                                                  in
                                               Prims.strcat uu____3651
                                                 uu____3652
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3650
                                              in
                                           debug_log env uu____3649);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3726 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3728 =
                                  let uu____3729 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3729.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3728
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
                   (let uu____3869 = try_get_fv t1  in
                    match uu____3869 with
                    | (fv,uu____3875) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3896 =
                      let uu____3897 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3897
                       in
                    debug_log env uu____3896);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3899 =
                      FStar_List.fold_left
                        (fun uu____3916  ->
                           fun b  ->
                             match uu____3916 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3937 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____4010 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3937, uu____4010))) (true, env)
                        sbs1
                       in
                    match uu____3899 with | (b,uu____4020) -> b))
              | uu____4021 ->
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
              let uu____4112 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____4112 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____4134 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____4136 =
                      let uu____4137 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____4137
                       in
                    debug_log env uu____4136);
                   (let uu____4138 =
                      let uu____4139 = FStar_Syntax_Subst.compress dt  in
                      uu____4139.FStar_Syntax_Syntax.n  in
                    match uu____4138 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____4142 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4145) ->
                        let dbs1 =
                          let uu____4169 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____4169  in
                        let dbs2 =
                          let uu____4207 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____4207 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____4212 =
                            let uu____4213 =
                              let uu____4214 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____4214 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____4213
                             in
                          debug_log env uu____4212);
                         (let uu____4219 =
                            FStar_List.fold_left
                              (fun uu____4236  ->
                                 fun b  ->
                                   match uu____4236 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____4257 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____4330 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____4257, uu____4330)))
                              (true, env) dbs3
                             in
                          match uu____4219 with | (b,uu____4340) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____4341,uu____4342) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4443 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4469 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4485,uu____4486,uu____4487) -> (lid, us, bs)
        | uu____4496 -> failwith "Impossible!"  in
      match uu____4469 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4506 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4506 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4529 =
                 let uu____4532 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4532  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4544 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4544
                      unfolded_inductives env2) uu____4529)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4624,uu____4625,t,uu____4627,uu____4628,uu____4629) -> t
    | uu____4634 -> failwith "Impossible!"
  
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
          let uu____4653 =
            let uu____4654 = FStar_Syntax_Subst.compress dt1  in
            uu____4654.FStar_Syntax_Syntax.n  in
          match uu____4653 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4658) ->
              let dbs1 =
                let uu____4682 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4682  in
              let dbs2 =
                let uu____4720 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4720 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4735 =
                           let uu____4736 =
                             let uu____4737 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4737]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4736
                            in
                         uu____4735 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4742 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4742 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4750 =
                       let uu____4751 =
                         let uu____4752 =
                           let uu____4753 =
                             let uu____4754 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4754
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4753  in
                         [uu____4752]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4751
                        in
                     uu____4750 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4771 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____4843,uu____4844,uu____4845,uu____4846,uu____4847)
                  -> lid
              | uu____4856 -> failwith "Impossible!"  in
            let uu____4857 = acc  in
            match uu____4857 with
            | (uu____4890,en,uu____4892,uu____4893) ->
                let uu____4906 =
                  FStar_TypeChecker_Util.get_optimized_haseq_axiom en ty
                    usubst us
                   in
                (match uu____4906 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____4943 = acc  in
                     (match uu____4943 with
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
                                     (uu____5005,uu____5006,uu____5007,t_lid,uu____5009,uu____5010)
                                     -> t_lid = lid
                                 | uu____5015 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5022 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5022)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5023 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5026 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5023, uu____5026)))
  
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
                  (uu____5109,us,uu____5111,uu____5112,uu____5113,uu____5114)
                  -> us
              | uu____5123 -> failwith "Impossible!"  in
            let uu____5124 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____5124 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____5149 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____5149 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____5207 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____5207 with
                       | (phi1,uu____5215) ->
                           ((let uu____5217 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____5217
                             then
                               let uu____5218 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____5218
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____5235  ->
                                      match uu____5235 with
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
                let uu____5287 =
                  let uu____5288 = FStar_Syntax_Subst.compress t  in
                  uu____5288.FStar_Syntax_Syntax.n  in
                match uu____5287 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5295) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5328 = is_mutual t'  in
                    if uu____5328
                    then true
                    else
                      (let uu____5330 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5330)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5346) -> is_mutual t'
                | uu____5351 -> false
              
              and exists_mutual uu___55_5352 =
                match uu___55_5352 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5371 =
                let uu____5372 = FStar_Syntax_Subst.compress dt1  in
                uu____5372.FStar_Syntax_Syntax.n  in
              match uu____5371 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5378) ->
                  let dbs1 =
                    let uu____5402 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5402  in
                  let dbs2 =
                    let uu____5440 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5440 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5458 =
                               let uu____5459 =
                                 let uu____5460 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5460]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5459
                                in
                             uu____5458 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5464 = is_mutual sort  in
                             if uu____5464
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
                           let uu____5474 =
                             let uu____5475 =
                               let uu____5476 =
                                 let uu____5477 =
                                   let uu____5478 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5478 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5477  in
                               [uu____5476]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5475
                              in
                           uu____5474 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5495 -> acc
  
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
              let uu____5532 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5554,bs,t,uu____5557,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5569 -> failwith "Impossible!"  in
              match uu____5532 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5592 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5592 t  in
                  let uu____5599 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5599 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____5615 =
                           let uu____5616 = FStar_Syntax_Subst.compress t2
                              in
                           uu____5616.FStar_Syntax_Syntax.n  in
                         match uu____5615 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____5626) ->
                             ibs
                         | uu____5643 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____5650 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____5651 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____5650
                           uu____5651
                          in
                       let ind1 =
                         let uu____5657 =
                           let uu____5658 =
                             FStar_List.map
                               (fun uu____5671  ->
                                  match uu____5671 with
                                  | (bv,aq) ->
                                      let uu____5682 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5682, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____5658  in
                         uu____5657 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____5688 =
                           let uu____5689 =
                             FStar_List.map
                               (fun uu____5702  ->
                                  match uu____5702 with
                                  | (bv,aq) ->
                                      let uu____5713 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____5713, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5689  in
                         uu____5688 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____5719 =
                           let uu____5720 =
                             let uu____5721 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____5721]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5720
                            in
                         uu____5719 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____5735,uu____5736,uu____5737,t_lid,uu____5739,uu____5740)
                                  -> t_lid = lid
                              | uu____5745 -> failwith "Impossible")
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
                         let uu___63_5751 = fml  in
                         let uu____5752 =
                           let uu____5753 =
                             let uu____5760 =
                               let uu____5761 =
                                 let uu____5772 =
                                   let uu____5775 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____5775]  in
                                 [uu____5772]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____5761
                                in
                             (fml, uu____5760)  in
                           FStar_Syntax_Syntax.Tm_meta uu____5753  in
                         {
                           FStar_Syntax_Syntax.n = uu____5752;
                           FStar_Syntax_Syntax.pos =
                             (uu___63_5751.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___63_5751.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5788 =
                                  let uu____5789 =
                                    let uu____5790 =
                                      let uu____5791 =
                                        let uu____5792 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5792
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5791
                                       in
                                    [uu____5790]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5789
                                   in
                                uu____5788 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____5817 =
                                  let uu____5818 =
                                    let uu____5819 =
                                      let uu____5820 =
                                        let uu____5821 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5821
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____5820
                                       in
                                    [uu____5819]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____5818
                                   in
                                uu____5817 FStar_Pervasives_Native.None
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
                       (lid,uu____5906,uu____5907,uu____5908,uu____5909,uu____5910)
                       -> lid
                   | uu____5919 -> failwith "Impossible!") tcs
               in
            let uu____5920 =
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____5932,uu____5933,uu____5934,uu____5935) ->
                  (lid, us)
              | uu____5944 -> failwith "Impossible!"  in
            match uu____5920 with
            | (lid,us) ->
                let uu____5953 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____5953 with
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
                         let uu____5980 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env1 uu____5980 fml []
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
          let uu____6026 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___56_6051  ->
                    match uu___56_6051 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6052;
                        FStar_Syntax_Syntax.sigrng = uu____6053;
                        FStar_Syntax_Syntax.sigquals = uu____6054;
                        FStar_Syntax_Syntax.sigmeta = uu____6055;
                        FStar_Syntax_Syntax.sigattrs = uu____6056;_} -> true
                    | uu____6077 -> false))
             in
          match uu____6026 with
          | (tys,datas) ->
              ((let uu____6099 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___57_6108  ->
                          match uu___57_6108 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6109;
                              FStar_Syntax_Syntax.sigrng = uu____6110;
                              FStar_Syntax_Syntax.sigquals = uu____6111;
                              FStar_Syntax_Syntax.sigmeta = uu____6112;
                              FStar_Syntax_Syntax.sigattrs = uu____6113;_} ->
                              false
                          | uu____6132 -> true))
                   in
                if uu____6099
                then
                  let uu____6133 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6133
                else ());
               (let env0 = env  in
                let uu____6136 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____6175  ->
                         match uu____6175 with
                         | (env1,all_tcs,g) ->
                             let uu____6215 = tc_tycon env1 tc  in
                             (match uu____6215 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____6242 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____6242
                                    then
                                      let uu____6243 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____6243
                                    else ());
                                   (let uu____6245 =
                                      let uu____6246 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____6246
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____6245))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____6136 with
                | (env1,tcs,g) ->
                    let uu____6292 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____6314  ->
                             match uu____6314 with
                             | (datas1,g1) ->
                                 let uu____6333 =
                                   let uu____6338 = tc_data env1 tcs  in
                                   uu____6338 se  in
                                 (match uu____6333 with
                                  | (data,g') ->
                                      let uu____6353 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____6353))) datas
                        ([], g)
                       in
                    (match uu____6292 with
                     | (datas1,g1) ->
                         let uu____6374 =
                           generalize_and_inst_within env0 g1 tcs datas1  in
                         (match uu____6374 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____6404 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____6405 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____6404;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____6405
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs1,binders,typ,uu____6431,uu____6432)
                                           ->
                                           let fail expected inferred =
                                             let uu____6448 =
                                               let uu____6453 =
                                                 let uu____6454 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____6455 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____6454 uu____6455
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____6453)
                                                in
                                             FStar_Errors.raise_error
                                               uu____6448
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____6456 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____6456 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____6472) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____6493 ->
                                                        let uu____6494 =
                                                          let uu____6497 =
                                                            let uu____6498 =
                                                              let uu____6511
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
                                                              (binders,
                                                                uu____6511)
                                                               in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____6498
                                                             in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____6497
                                                           in
                                                        uu____6494
                                                          FStar_Pervasives_Native.None
                                                          se.FStar_Syntax_Syntax.sigrng
                                                     in
                                                  (univs1, body)  in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ1))
                                                then
                                                  let uu____6517 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____6517 with
                                                   | (uu____6522,inferred) ->
                                                       let uu____6524 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____6524 with
                                                        | (uu____6529,expected)
                                                            ->
                                                            let uu____6531 =
                                                              FStar_TypeChecker_Rel.teq_nosmt
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____6531
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail expected_typ1
                                                    inferred_typ)
                                       | uu____6534 -> ()));
                               (sig_bndle, tcs1, datas2))))))
  