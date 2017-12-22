open Prims
let tc_tycon:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let uu____40 = FStar_Syntax_Subst.open_term tps k in
          (match uu____40 with
           | (tps1,k1) ->
               let uu____55 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____55 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____77 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____77 with
                     | (indices,t) ->
                         let uu____116 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____116 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____137 =
                                let uu____142 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____142 with
                                | (t1,uu____154,g) ->
                                    let uu____156 =
                                      let uu____157 =
                                        let uu____158 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____158 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____157 in
                                    (t1, uu____156) in
                              (match uu____137 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____172 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____172 in
                                   let uu____175 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____175 with
                                    | (t_type,u) ->
                                        ((let uu____191 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____191);
                                         (let t_tc =
                                            let uu____195 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____195 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____205 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____205,
                                            (let uu___57_211 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___57_211.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___57_211.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___57_211.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___57_211.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____218 -> failwith "impossible"
let tc_data:
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2
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
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____331 in
                           FStar_Ident.lid_equals tc_lid uu____330 in
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
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____410 =
                                  let uu____417 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____417, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____410
                            | uu____424 -> failwith "Impossible")
                         else FStar_Pervasives_Native.None) in
              match tps_u_opt with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedDataConstructor,
                        "Unexpected data constructor")
                      se.FStar_Syntax_Syntax.sigrng in
            (match uu____275 with
             | (env1,tps,u_tc) ->
                 let uu____495 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____509 =
                     let uu____510 = FStar_Syntax_Subst.compress t1 in
                     uu____510.FStar_Syntax_Syntax.n in
                   match uu____509 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____543 = FStar_Util.first_N ntps bs in
                       (match uu____543 with
                        | (uu____576,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
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
                                                x))) in
                            let uu____634 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____634)
                   | uu____635 -> ([], t1) in
                 (match uu____495 with
                  | (arguments,result) ->
                      ((let uu____669 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____669
                        then
                          let uu____670 = FStar_Syntax_Print.lid_to_string c in
                          let uu____671 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____672 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____670
                            uu____671 uu____672
                        else ());
                       (let uu____674 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____674 with
                        | (arguments1,env',us) ->
                            let uu____688 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____688 with
                             | (result1,res_lcomp) ->
                                 ((let uu____700 =
                                     let uu____701 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____701.FStar_Syntax_Syntax.n in
                                   match uu____700 with
                                   | FStar_Syntax_Syntax.Tm_type uu____704 ->
                                       ()
                                   | ty ->
                                       let uu____706 =
                                         let uu____711 =
                                           let uu____712 =
                                             FStar_Syntax_Print.term_to_string
                                               result1 in
                                           let uu____713 =
                                             FStar_Syntax_Print.term_to_string
                                               res_lcomp.FStar_Syntax_Syntax.res_typ in
                                           FStar_Util.format2
                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                             uu____712 uu____713 in
                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                           uu____711) in
                                       FStar_Errors.raise_error uu____706
                                         se.FStar_Syntax_Syntax.sigrng);
                                  (let uu____714 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____714 with
                                   | (head1,uu____734) ->
                                       ((let uu____756 =
                                           let uu____757 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____757.FStar_Syntax_Syntax.n in
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
                                                     tc_lid in
                                                 let uu____769 =
                                                   FStar_Syntax_Print.term_to_string
                                                     head1 in
                                                 FStar_Util.format2
                                                   "Expected a constructor of type %s; got %s"
                                                   uu____768 uu____769 in
                                               (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                 uu____767) in
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
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____790)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
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
                                                                   true))))) in
                                             FStar_List.append uu____801
                                               arguments1 in
                                           let uu____852 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____794
                                             uu____852 in
                                         ((let uu___58_856 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___58_856.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___58_856.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___58_856.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___58_856.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____863 -> failwith "impossible"
let generalize_and_inst_within:
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs in
          let g1 =
            let uu___59_920 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___59_920.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___59_920.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___59_920.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____930 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____930
           then
             let uu____931 = FStar_TypeChecker_Rel.guard_to_string env g1 in
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
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____981 in
                              FStar_Syntax_Syntax.null_binder uu____980
                          | uu____988 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1004,uu____1005,t,uu____1007,uu____1008,uu____1009)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1014 -> failwith "Impossible")) in
           let t =
             let uu____1018 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1018 in
           (let uu____1022 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1022
            then
              let uu____1023 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1023
            else ());
           (let uu____1025 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1025 with
            | (uvs,t1) ->
                ((let uu____1041 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1041
                  then
                    let uu____1042 =
                      let uu____1043 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1043
                        (FStar_String.concat ", ") in
                    let uu____1054 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1042 uu____1054
                  else ());
                 (let uu____1056 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1056 with
                  | (uvs1,t2) ->
                      let uu____1071 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1071 with
                       | (args,uu____1093) ->
                           let uu____1110 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
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
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1238 =
                                                    let uu____1251 =
                                                      let uu____1252 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1252.FStar_Syntax_Syntax.n in
                                                    match uu____1251 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1285 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
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
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1380 -> ([], ty) in
                                                  (match uu____1238 with
                                                   | (tps1,t3) ->
                                                       let uu___60_1409 = se in
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
                                                           (uu___60_1409.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___60_1409.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___60_1409.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___60_1409.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1422 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1428 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___53_1470  ->
                                                match uu___53_1470 with
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
                                                    failwith "Impossible")) in
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
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1543
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___61_1544 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___61_1544.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___61_1544.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___61_1544.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___61_1544.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1547 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1558 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1558
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1566 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1566
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1580 =
      let uu____1581 = FStar_Syntax_Subst.compress t in
      uu____1581.FStar_Syntax_Syntax.n in
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
let already_unfolded:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1652 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____1746  ->
               match uu____1746 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1781 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1781 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1652
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1953 =
             let uu____1954 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1954 in
           debug_log env uu____1953);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1957 =
              let uu____1958 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1958 in
            debug_log env uu____1957);
           (let uu____1961 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1961) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1971 =
                  let uu____1972 = FStar_Syntax_Subst.compress btype1 in
                  uu____1972.FStar_Syntax_Syntax.n in
                match uu____1971 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1997 = try_get_fv t in
                    (match uu____1997 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2013  ->
                                 match uu____2013 with
                                 | (t1,uu____2019) ->
                                     let uu____2020 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2020) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2062 =
                        let uu____2063 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2063 in
                      if uu____2062
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2075  ->
                               match uu____2075 with
                               | (b,uu____2081) ->
                                   let uu____2082 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2082) sbs)
                           &&
                           ((let uu____2087 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2087 with
                             | (uu____2092,return_type) ->
                                 let uu____2094 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2094)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2115 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2117 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2120) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2147) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2173,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2231  ->
                          match uu____2231 with
                          | (p,uu____2243,t) ->
                              let bs =
                                let uu____2256 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2256 in
                              let uu____2259 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2259 with
                               | (bs1,t1) ->
                                   let uu____2266 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2266)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2288,uu____2289)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2351 ->
                    ((let uu____2353 =
                        let uu____2354 =
                          let uu____2355 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2356 =
                            let uu____2357 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2357 in
                          Prims.strcat uu____2355 uu____2356 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2354 in
                      debug_log env uu____2353);
                     false)))))
and ty_nested_positive_in_inductive:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              (let uu____2375 =
                 let uu____2376 =
                   let uu____2377 =
                     let uu____2378 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2378 in
                   Prims.strcat ilid.FStar_Ident.str uu____2377 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2376 in
               debug_log env uu____2375);
              (let uu____2379 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2379 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2394 =
                        already_unfolded ilid args unfolded env in
                      if uu____2394
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2419 =
                            let uu____2420 =
                              let uu____2421 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2421
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2420 in
                          debug_log env uu____2419);
                         (let uu____2423 =
                            let uu____2424 = FStar_ST.op_Bang unfolded in
                            let uu____2499 =
                              let uu____2506 =
                                let uu____2519 =
                                  let uu____2528 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2528 in
                                (ilid, uu____2519) in
                              [uu____2506] in
                            FStar_List.append uu____2424 uu____2499 in
                          FStar_ST.op_Colon_Equals unfolded uu____2423);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))
and ty_nested_positive_in_dlid:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
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
                  (let uu____2716 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2716 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2738 ->
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
                         (let uu____2741 =
                            let uu____2742 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2742 in
                          debug_log env uu____2741);
                         (let uu____2743 =
                            let uu____2744 = FStar_Syntax_Subst.compress dt1 in
                            uu____2744.FStar_Syntax_Syntax.n in
                          match uu____2743 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2766 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2766 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2815 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2815 dbs1 in
                                    let c1 =
                                      let uu____2819 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2819 c in
                                    let uu____2822 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2822 with
                                     | (args1,uu____2850) ->
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
                                             args1 in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2 in
                                         let c2 =
                                           let uu____2922 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2922 c1 in
                                         ((let uu____2930 =
                                             let uu____2931 =
                                               let uu____2932 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2933 =
                                                 let uu____2934 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2934 in
                                               Prims.strcat uu____2932
                                                 uu____2933 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2931 in
                                           debug_log env uu____2930);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2955 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2957 =
                                  let uu____2958 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2958.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2957
                                  ilid num_ibs unfolded env))))))
and ty_nested_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
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
                   (let uu____3020 = try_get_fv t1 in
                    match uu____3020 with
                    | (fv,uu____3026) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3047 =
                      let uu____3048 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3048 in
                    debug_log env uu____3047);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____3050 =
                      FStar_List.fold_left
                        (fun uu____3067  ->
                           fun b  ->
                             match uu____3067 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3088 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____3109 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____3088, uu____3109))) (true, env)
                        sbs1 in
                    match uu____3050 with | (b,uu____3119) -> b))
              | uu____3120 ->
                  failwith "Nested positive check, unhandled case"
let ty_positive_in_datacon:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____3159 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3159 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3181 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3183 =
                      let uu____3184 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____3184 in
                    debug_log env uu____3183);
                   (let uu____3185 =
                      let uu____3186 = FStar_Syntax_Subst.compress dt in
                      uu____3186.FStar_Syntax_Syntax.n in
                    match uu____3185 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3189 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3192) ->
                        let dbs1 =
                          let uu____3216 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3216 in
                        let dbs2 =
                          let uu____3254 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3254 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3259 =
                            let uu____3260 =
                              let uu____3261 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____3261 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3260 in
                          debug_log env uu____3259);
                         (let uu____3266 =
                            FStar_List.fold_left
                              (fun uu____3283  ->
                                 fun b  ->
                                   match uu____3283 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3304 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3325 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3304, uu____3325)))
                              (true, env) dbs3 in
                          match uu____3266 with | (b,uu____3335) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3336,uu____3337) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3386 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3412 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3428,uu____3429,uu____3430) -> (lid, us, bs)
        | uu____3439 -> failwith "Impossible!" in
      match uu____3412 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3449 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3449 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3472 =
                 let uu____3475 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3475 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3487 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3487
                      unfolded_inductives env2) uu____3472)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3515,uu____3516,t,uu____3518,uu____3519,uu____3520) -> t
    | uu____3525 -> failwith "Impossible!"
let optimized_haseq_soundness_for_data:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data in
          let dt1 = FStar_Syntax_Subst.subst usubst dt in
          let uu____3544 =
            let uu____3545 = FStar_Syntax_Subst.compress dt1 in
            uu____3545.FStar_Syntax_Syntax.n in
          match uu____3544 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3549) ->
              let dbs1 =
                let uu____3573 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3573 in
              let dbs2 =
                let uu____3611 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3611 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3626 =
                           let uu____3627 =
                             let uu____3628 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3628] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3627 in
                         uu____3626 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3633 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3633 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3641 =
                       let uu____3642 =
                         let uu____3643 =
                           let uu____3644 =
                             let uu____3645 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3645
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3644 in
                         [uu____3643] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3642 in
                     uu____3641 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3662 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty:
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
              FStar_Pervasives_Native.tuple4
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let uu____3732 =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____3754,bs,t,uu____3757,d_lids) ->
                  (lid, bs, t, d_lids)
              | uu____3769 -> failwith "Impossible!" in
            match uu____3732 with
            | (lid,bs,t,d_lids) ->
                let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                let t1 =
                  let uu____3808 =
                    FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                      usubst in
                  FStar_Syntax_Subst.subst uu____3808 t in
                let uu____3815 = FStar_Syntax_Subst.open_term bs1 t1 in
                (match uu____3815 with
                 | (bs2,t2) ->
                     let ibs =
                       let uu____3847 =
                         let uu____3848 = FStar_Syntax_Subst.compress t2 in
                         uu____3848.FStar_Syntax_Syntax.n in
                       match uu____3847 with
                       | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3858) -> ibs
                       | uu____3875 -> [] in
                     let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                     let ind =
                       let uu____3882 =
                         FStar_Syntax_Syntax.fvar lid
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       let uu____3883 =
                         FStar_List.map
                           (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____3882 uu____3883 in
                     let ind1 =
                       let uu____3889 =
                         let uu____3890 =
                           FStar_List.map
                             (fun uu____3903  ->
                                match uu____3903 with
                                | (bv,aq) ->
                                    let uu____3914 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3914, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____3890 in
                       uu____3889 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let ind2 =
                       let uu____3920 =
                         let uu____3921 =
                           FStar_List.map
                             (fun uu____3934  ->
                                match uu____3934 with
                                | (bv,aq) ->
                                    let uu____3945 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3945, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3921 in
                       uu____3920 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let haseq_ind =
                       let uu____3951 =
                         let uu____3952 =
                           let uu____3953 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____3953] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____3952 in
                       uu____3951 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let bs' =
                       FStar_List.filter
                         (fun b  ->
                            let uu____3979 = acc in
                            match uu____3979 with
                            | (uu____3994,en,uu____3996,uu____3997) ->
                                let uu____4010 =
                                  let uu____4011 =
                                    FStar_Syntax_Util.type_u () in
                                  FStar_Pervasives_Native.fst uu____4011 in
                                FStar_TypeChecker_Rel.subtype_nosmt en
                                  (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                  uu____4010) bs2 in
                     let haseq_bs =
                       FStar_List.fold_left
                         (fun t3  ->
                            fun b  ->
                              let uu____4022 =
                                let uu____4023 =
                                  let uu____4024 =
                                    let uu____4025 =
                                      let uu____4026 =
                                        FStar_Syntax_Syntax.bv_to_name
                                          (FStar_Pervasives_Native.fst b) in
                                      FStar_Syntax_Syntax.as_arg uu____4026 in
                                    [uu____4025] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.t_haseq uu____4024 in
                                uu____4023 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange in
                              FStar_Syntax_Util.mk_conj t3 uu____4022)
                         FStar_Syntax_Util.t_true bs' in
                     let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                     let fml1 =
                       let uu___62_4033 = fml in
                       let uu____4034 =
                         let uu____4035 =
                           let uu____4042 =
                             let uu____4043 =
                               let uu____4054 =
                                 let uu____4057 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____4057] in
                               [uu____4054] in
                             FStar_Syntax_Syntax.Meta_pattern uu____4043 in
                           (fml, uu____4042) in
                         FStar_Syntax_Syntax.Tm_meta uu____4035 in
                       {
                         FStar_Syntax_Syntax.n = uu____4034;
                         FStar_Syntax_Syntax.pos =
                           (uu___62_4033.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___62_4033.FStar_Syntax_Syntax.vars)
                       } in
                     let fml2 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____4070 =
                                let uu____4071 =
                                  let uu____4072 =
                                    let uu____4073 =
                                      let uu____4074 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____4074
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____4073 in
                                  [uu____4072] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____4071 in
                              uu____4070 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) ibs1 fml1 in
                     let fml3 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____4099 =
                                let uu____4100 =
                                  let uu____4101 =
                                    let uu____4102 =
                                      let uu____4103 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____4103
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____4102 in
                                  [uu____4101] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____4100 in
                              uu____4099 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) bs2 fml2 in
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
                     let uu____4123 = acc in
                     (match uu____4123 with
                      | (l_axioms,env,guard',cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs2 in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs1 in
                          let t_datas =
                            FStar_List.filter
                              (fun s  ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____4185,uu____4186,uu____4187,t_lid,uu____4189,uu____4190)
                                     -> t_lid = lid
                                 | uu____4195 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4202 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs2 in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4202)
                              FStar_Syntax_Util.t_true t_datas in
                          let axiom_lid =
                            FStar_Ident.lid_of_ids
                              (FStar_List.append lid.FStar_Ident.ns
                                 [FStar_Ident.id_of_text
                                    (Prims.strcat
                                       (lid.FStar_Ident.ident).FStar_Ident.idText
                                       "_haseq")]) in
                          let uu____4204 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____4207 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml3)]),
                            env2, uu____4204, uu____4207)))
let optimized_haseq_scheme:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          fun tc_assume  ->
            let us =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____4290,us,uu____4292,uu____4293,uu____4294,uu____4295)
                  -> us
              | uu____4304 -> failwith "Impossible!" in
            let uu____4305 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____4305 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____4330 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____4330 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____4388 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____4388 with
                       | (phi1,uu____4396) ->
                           ((let uu____4398 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____4398
                             then
                               let uu____4399 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4399
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____4416  ->
                                      match uu____4416 with
                                      | (lid,fml) ->
                                          let se =
                                            tc_assume env2 lid fml []
                                              FStar_Range.dummyRange in
                                          FStar_List.append l [se]) [] axioms in
                             (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                               "haseq";
                             ses)))))
let unoptimized_haseq_data:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____4468 =
                  let uu____4469 = FStar_Syntax_Subst.compress t in
                  uu____4469.FStar_Syntax_Syntax.n in
                match uu____4468 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4476) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4509 = is_mutual t' in
                    if uu____4509
                    then true
                    else
                      (let uu____4511 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4511)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4527) -> is_mutual t'
                | uu____4532 -> false
              and exists_mutual uu___54_4533 =
                match uu___54_4533 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4552 =
                let uu____4553 = FStar_Syntax_Subst.compress dt1 in
                uu____4553.FStar_Syntax_Syntax.n in
              match uu____4552 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4559) ->
                  let dbs1 =
                    let uu____4583 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4583 in
                  let dbs2 =
                    let uu____4621 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4621 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4639 =
                               let uu____4640 =
                                 let uu____4641 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4641] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4640 in
                             uu____4639 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4645 = is_mutual sort in
                             if uu____4645
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____4655 =
                             let uu____4656 =
                               let uu____4657 =
                                 let uu____4658 =
                                   let uu____4659 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4659 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4658 in
                               [uu____4657] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4656 in
                           uu____4655 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4676 -> acc
let unoptimized_haseq_ty:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun all_datas_in_the_bundle  ->
    fun mutuals  ->
      fun usubst  ->
        fun us  ->
          fun acc  ->
            fun ty  ->
              let uu____4713 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4735,bs,t,uu____4738,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4750 -> failwith "Impossible!" in
              match uu____4713 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____4773 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____4773 t in
                  let uu____4780 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____4780 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4796 =
                           let uu____4797 = FStar_Syntax_Subst.compress t2 in
                           uu____4797.FStar_Syntax_Syntax.n in
                         match uu____4796 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4807) ->
                             ibs
                         | uu____4824 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____4831 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____4832 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4831
                           uu____4832 in
                       let ind1 =
                         let uu____4838 =
                           let uu____4839 =
                             FStar_List.map
                               (fun uu____4852  ->
                                  match uu____4852 with
                                  | (bv,aq) ->
                                      let uu____4863 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4863, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4839 in
                         uu____4838 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____4869 =
                           let uu____4870 =
                             FStar_List.map
                               (fun uu____4883  ->
                                  match uu____4883 with
                                  | (bv,aq) ->
                                      let uu____4894 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4894, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4870 in
                         uu____4869 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____4900 =
                           let uu____4901 =
                             let uu____4902 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____4902] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4901 in
                         uu____4900 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4916,uu____4917,uu____4918,t_lid,uu____4920,uu____4921)
                                  -> t_lid = lid
                              | uu____4926 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___63_4932 = fml in
                         let uu____4933 =
                           let uu____4934 =
                             let uu____4941 =
                               let uu____4942 =
                                 let uu____4953 =
                                   let uu____4956 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____4956] in
                                 [uu____4953] in
                               FStar_Syntax_Syntax.Meta_pattern uu____4942 in
                             (fml, uu____4941) in
                           FStar_Syntax_Syntax.Tm_meta uu____4934 in
                         {
                           FStar_Syntax_Syntax.n = uu____4933;
                           FStar_Syntax_Syntax.pos =
                             (uu___63_4932.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___63_4932.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4969 =
                                  let uu____4970 =
                                    let uu____4971 =
                                      let uu____4972 =
                                        let uu____4973 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4973
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4972 in
                                    [uu____4971] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4970 in
                                uu____4969 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4998 =
                                  let uu____4999 =
                                    let uu____5000 =
                                      let uu____5001 =
                                        let uu____5002 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____5002
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____5001 in
                                    [uu____5000] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4999 in
                                uu____4998 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2 in
                       FStar_Syntax_Util.mk_conj acc fml3)
let unoptimized_haseq_scheme:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t ->
          (FStar_TypeChecker_Env.env_t ->
             FStar_Ident.lident ->
               FStar_Syntax_Syntax.formula ->
                 FStar_Syntax_Syntax.qualifier Prims.list ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
            -> FStar_Syntax_Syntax.sigelt Prims.list
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
                       (lid,uu____5087,uu____5088,uu____5089,uu____5090,uu____5091)
                       -> lid
                   | uu____5100 -> failwith "Impossible!") tcs in
            let uu____5101 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____5113,uu____5114,uu____5115,uu____5116) ->
                  (lid, us)
              | uu____5125 -> failwith "Impossible!" in
            match uu____5101 with
            | (lid,us) ->
                let uu____5134 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____5134 with
                 | (usubst,us1) ->
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
                         let uu____5161 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____5161 fml []
                           FStar_Range.dummyRange in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
let check_inductive_well_typedness:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____5207 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___55_5232  ->
                    match uu___55_5232 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5233;
                        FStar_Syntax_Syntax.sigrng = uu____5234;
                        FStar_Syntax_Syntax.sigquals = uu____5235;
                        FStar_Syntax_Syntax.sigmeta = uu____5236;
                        FStar_Syntax_Syntax.sigattrs = uu____5237;_} -> true
                    | uu____5258 -> false)) in
          match uu____5207 with
          | (tys,datas) ->
              ((let uu____5280 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___56_5289  ->
                          match uu___56_5289 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5290;
                              FStar_Syntax_Syntax.sigrng = uu____5291;
                              FStar_Syntax_Syntax.sigquals = uu____5292;
                              FStar_Syntax_Syntax.sigmeta = uu____5293;
                              FStar_Syntax_Syntax.sigattrs = uu____5294;_} ->
                              false
                          | uu____5313 -> true)) in
                if uu____5280
                then
                  let uu____5314 = FStar_TypeChecker_Env.get_range env in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____5314
                else ());
               (let env0 = env in
                let uu____5317 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____5356  ->
                         match uu____5356 with
                         | (env1,all_tcs,g) ->
                             let uu____5396 = tc_tycon env1 tc in
                             (match uu____5396 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____5423 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____5423
                                    then
                                      let uu____5424 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____5424
                                    else ());
                                   (let uu____5426 =
                                      let uu____5427 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____5427 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____5426))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____5317 with
                | (env1,tcs,g) ->
                    let uu____5473 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____5495  ->
                             match uu____5495 with
                             | (datas1,g1) ->
                                 let uu____5514 =
                                   let uu____5519 = tc_data env1 tcs in
                                   uu____5519 se in
                                 (match uu____5514 with
                                  | (data,g') ->
                                      let uu____5534 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____5534))) datas
                        ([], g) in
                    (match uu____5473 with
                     | (datas1,g1) ->
                         let uu____5555 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____5555 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____5585 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____5586 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____5585;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____5586
                                } in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs1,binders,typ,uu____5612,uu____5613)
                                           ->
                                           let fail expected inferred =
                                             let uu____5629 =
                                               let uu____5634 =
                                                 let uu____5635 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected in
                                                 let uu____5636 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____5635 uu____5636 in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____5634) in
                                             FStar_Errors.raise_error
                                               uu____5629
                                               se.FStar_Syntax_Syntax.sigrng in
                                           let uu____5637 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____5637 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____5653) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____5674 ->
                                                        let uu____5675 =
                                                          let uu____5678 =
                                                            let uu____5679 =
                                                              let uu____5692
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ in
                                                              (binders,
                                                                uu____5692) in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____5679 in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____5678 in
                                                        uu____5675
                                                          FStar_Pervasives_Native.None
                                                          se.FStar_Syntax_Syntax.sigrng in
                                                  (univs1, body) in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ1))
                                                then
                                                  let uu____5698 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____5698 with
                                                   | (uu____5703,inferred) ->
                                                       let uu____5705 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1 in
                                                       (match uu____5705 with
                                                        | (uu____5710,expected)
                                                            ->
                                                            let uu____5712 =
                                                              FStar_TypeChecker_Rel.teq_nosmt
                                                                env0 inferred
                                                                expected in
                                                            if uu____5712
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail expected_typ1
                                                    inferred_typ)
                                       | uu____5715 -> ()));
                               (sig_bndle, tcs1, datas2))))))