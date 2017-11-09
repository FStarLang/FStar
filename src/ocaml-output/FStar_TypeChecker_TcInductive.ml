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
                                            (let uu___339_211 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___339_211.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___339_211.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___339_211.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___339_211.FStar_Syntax_Syntax.sigattrs)
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
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng))) in
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
                                         let uu____707 =
                                           let uu____712 =
                                             let uu____713 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____714 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____713 uu____714 in
                                           (uu____712,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____707 in
                                       FStar_Exn.raise uu____706);
                                  (let uu____715 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____715 with
                                   | (head1,uu____735) ->
                                       ((let uu____757 =
                                           let uu____758 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____758.FStar_Syntax_Syntax.n in
                                         match uu____757 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____762 ->
                                             let uu____763 =
                                               let uu____764 =
                                                 let uu____769 =
                                                   let uu____770 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____771 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____770 uu____771 in
                                                 (uu____769,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____764 in
                                             FStar_Exn.raise uu____763);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____784  ->
                                                  fun u_x  ->
                                                    match uu____784 with
                                                    | (x,uu____791) ->
                                                        let uu____792 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____792)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
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
                                                                   true))))) in
                                             FStar_List.append uu____803
                                               arguments1 in
                                           let uu____854 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____796
                                             uu____854 in
                                         ((let uu___340_858 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___340_858.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___340_858.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___340_858.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___340_858.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____865 -> failwith "impossible"
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
            let uu___341_922 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___341_922.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___341_922.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___341_922.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____932 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____932
           then
             let uu____933 = FStar_TypeChecker_Rel.guard_to_string env g1 in
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
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____983 in
                              FStar_Syntax_Syntax.null_binder uu____982
                          | uu____990 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1006,uu____1007,t,uu____1009,uu____1010,uu____1011)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1016 -> failwith "Impossible")) in
           let t =
             let uu____1020 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1020 in
           (let uu____1024 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1024
            then
              let uu____1025 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1025
            else ());
           (let uu____1027 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1027 with
            | (uvs,t1) ->
                ((let uu____1043 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1043
                  then
                    let uu____1044 =
                      let uu____1045 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1045
                        (FStar_String.concat ", ") in
                    let uu____1056 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1044 uu____1056
                  else ());
                 (let uu____1058 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1058 with
                  | (uvs1,t2) ->
                      let uu____1073 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1073 with
                       | (args,uu____1095) ->
                           let uu____1112 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
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
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1240 =
                                                    let uu____1253 =
                                                      let uu____1254 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1254.FStar_Syntax_Syntax.n in
                                                    match uu____1253 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1287 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
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
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1382 -> ([], ty) in
                                                  (match uu____1240 with
                                                   | (tps1,t3) ->
                                                       let uu___342_1411 = se in
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
                                                           (uu___342_1411.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___342_1411.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___342_1411.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___342_1411.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1424 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1430 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___335_1472  ->
                                                match uu___335_1472 with
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
                                                    failwith "Impossible")) in
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
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1545
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___343_1546 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___343_1546.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___343_1546.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___343_1546.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___343_1546.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1549 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1560 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1560
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1568 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1568
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1582 =
      let uu____1583 = FStar_Syntax_Subst.compress t in
      uu____1583.FStar_Syntax_Syntax.n in
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
let already_unfolded:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1646 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____1730  ->
               match uu____1730 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1765 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1765 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1646
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1917 =
             let uu____1918 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1918 in
           debug_log env uu____1917);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1921 =
              let uu____1922 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1922 in
            debug_log env uu____1921);
           (let uu____1925 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1925) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1935 =
                  let uu____1936 = FStar_Syntax_Subst.compress btype1 in
                  uu____1936.FStar_Syntax_Syntax.n in
                match uu____1935 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1961 = try_get_fv t in
                    (match uu____1961 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1977  ->
                                 match uu____1977 with
                                 | (t1,uu____1983) ->
                                     let uu____1984 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1984) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2018 =
                        let uu____2019 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2019 in
                      if uu____2018
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2031  ->
                               match uu____2031 with
                               | (b,uu____2037) ->
                                   let uu____2038 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2038) sbs)
                           &&
                           ((let uu____2043 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2043 with
                             | (uu____2048,return_type) ->
                                 let uu____2050 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2050)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2063 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2065 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2068) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2087) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2105,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2163  ->
                          match uu____2163 with
                          | (p,uu____2175,t) ->
                              let bs =
                                let uu____2188 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2188 in
                              let uu____2191 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2191 with
                               | (bs1,t1) ->
                                   let uu____2198 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2198)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2212,uu____2213)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2267 ->
                    ((let uu____2269 =
                        let uu____2270 =
                          let uu____2271 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2272 =
                            let uu____2273 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2273 in
                          Prims.strcat uu____2271 uu____2272 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2270 in
                      debug_log env uu____2269);
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
              (let uu____2287 =
                 let uu____2288 =
                   let uu____2289 =
                     let uu____2290 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2290 in
                   Prims.strcat ilid.FStar_Ident.str uu____2289 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2288 in
               debug_log env uu____2287);
              (let uu____2291 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2291 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2306 =
                        already_unfolded ilid args unfolded env in
                      if uu____2306
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2323 =
                            let uu____2324 =
                              let uu____2325 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2325
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2324 in
                          debug_log env uu____2323);
                         (let uu____2327 =
                            let uu____2328 = FStar_ST.op_Bang unfolded in
                            let uu____2393 =
                              let uu____2400 =
                                let uu____2413 =
                                  let uu____2422 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2422 in
                                (ilid, uu____2413) in
                              [uu____2400] in
                            FStar_List.append uu____2328 uu____2393 in
                          FStar_ST.op_Colon_Equals unfolded uu____2327);
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
                  (let uu____2588 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2588 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2610 ->
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
                         (let uu____2613 =
                            let uu____2614 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2614 in
                          debug_log env uu____2613);
                         (let uu____2615 =
                            let uu____2616 = FStar_Syntax_Subst.compress dt1 in
                            uu____2616.FStar_Syntax_Syntax.n in
                          match uu____2615 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2638 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2638 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2687 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2687 dbs1 in
                                    let c1 =
                                      let uu____2691 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2691 c in
                                    let uu____2694 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2694 with
                                     | (args1,uu____2722) ->
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
                                           let uu____2794 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2794 c1 in
                                         ((let uu____2802 =
                                             let uu____2803 =
                                               let uu____2804 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2805 =
                                                 let uu____2806 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2806 in
                                               Prims.strcat uu____2804
                                                 uu____2805 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2803 in
                                           debug_log env uu____2802);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2819 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2821 =
                                  let uu____2822 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2822.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2821
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
                   (let uu____2872 = try_get_fv t1 in
                    match uu____2872 with
                    | (fv,uu____2878) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____2899 =
                      let uu____2900 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2900 in
                    debug_log env uu____2899);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____2902 =
                      FStar_List.fold_left
                        (fun uu____2919  ->
                           fun b  ->
                             match uu____2919 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____2940 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____2953 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____2940, uu____2953))) (true, env)
                        sbs1 in
                    match uu____2902 with | (b,uu____2963) -> b))
              | uu____2964 ->
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
              let uu____2995 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____2995 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3017 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3019 =
                      let uu____3020 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____3020 in
                    debug_log env uu____3019);
                   (let uu____3021 =
                      let uu____3022 = FStar_Syntax_Subst.compress dt in
                      uu____3022.FStar_Syntax_Syntax.n in
                    match uu____3021 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3025 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3028) ->
                        let dbs1 =
                          let uu____3052 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3052 in
                        let dbs2 =
                          let uu____3090 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3090 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3095 =
                            let uu____3096 =
                              let uu____3097 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____3097 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3096 in
                          debug_log env uu____3095);
                         (let uu____3102 =
                            FStar_List.fold_left
                              (fun uu____3119  ->
                                 fun b  ->
                                   match uu____3119 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3140 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3153 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3140, uu____3153)))
                              (true, env) dbs3 in
                          match uu____3102 with | (b,uu____3163) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3164,uu____3165) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3206 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3232 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3248,uu____3249,uu____3250) -> (lid, us, bs)
        | uu____3259 -> failwith "Impossible!" in
      match uu____3232 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3269 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3269 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3292 =
                 let uu____3295 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3295 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3307 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3307
                      unfolded_inductives env2) uu____3292)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3327,uu____3328,t,uu____3330,uu____3331,uu____3332) -> t
    | uu____3337 -> failwith "Impossible!"
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
          let uu____3356 =
            let uu____3357 = FStar_Syntax_Subst.compress dt1 in
            uu____3357.FStar_Syntax_Syntax.n in
          match uu____3356 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3361) ->
              let dbs1 =
                let uu____3385 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3385 in
              let dbs2 =
                let uu____3423 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3423 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3438 =
                           let uu____3439 =
                             let uu____3440 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3440] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3439 in
                         uu____3438 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3445 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3445 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3453 =
                       let uu____3454 =
                         let uu____3455 =
                           let uu____3456 =
                             let uu____3457 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3457
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3456 in
                         [uu____3455] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3454 in
                     uu____3453 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3474 -> FStar_Syntax_Util.t_true
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
            let uu____3544 =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____3566,bs,t,uu____3569,d_lids) ->
                  (lid, bs, t, d_lids)
              | uu____3581 -> failwith "Impossible!" in
            match uu____3544 with
            | (lid,bs,t,d_lids) ->
                let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                let t1 =
                  let uu____3620 =
                    FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                      usubst in
                  FStar_Syntax_Subst.subst uu____3620 t in
                let uu____3627 = FStar_Syntax_Subst.open_term bs1 t1 in
                (match uu____3627 with
                 | (bs2,t2) ->
                     let ibs =
                       let uu____3659 =
                         let uu____3660 = FStar_Syntax_Subst.compress t2 in
                         uu____3660.FStar_Syntax_Syntax.n in
                       match uu____3659 with
                       | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3670) -> ibs
                       | uu____3687 -> [] in
                     let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                     let ind =
                       let uu____3694 =
                         FStar_Syntax_Syntax.fvar lid
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       let uu____3695 =
                         FStar_List.map
                           (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____3694 uu____3695 in
                     let ind1 =
                       let uu____3701 =
                         let uu____3702 =
                           FStar_List.map
                             (fun uu____3715  ->
                                match uu____3715 with
                                | (bv,aq) ->
                                    let uu____3726 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3726, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____3702 in
                       uu____3701 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let ind2 =
                       let uu____3732 =
                         let uu____3733 =
                           FStar_List.map
                             (fun uu____3746  ->
                                match uu____3746 with
                                | (bv,aq) ->
                                    let uu____3757 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3757, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3733 in
                       uu____3732 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let haseq_ind =
                       let uu____3763 =
                         let uu____3764 =
                           let uu____3765 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____3765] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____3764 in
                       uu____3763 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let bs' =
                       FStar_List.filter
                         (fun b  ->
                            let uu____3791 = acc in
                            match uu____3791 with
                            | (uu____3806,en,uu____3808,uu____3809) ->
                                let opt =
                                  let uu____3825 =
                                    let uu____3826 =
                                      FStar_Syntax_Util.type_u () in
                                    FStar_Pervasives_Native.fst uu____3826 in
                                  FStar_TypeChecker_Rel.try_subtype' en
                                    (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    uu____3825 false in
                                (match opt with
                                 | FStar_Pervasives_Native.None  -> false
                                 | FStar_Pervasives_Native.Some uu____3831 ->
                                     true)) bs2 in
                     let haseq_bs =
                       FStar_List.fold_left
                         (fun t3  ->
                            fun b  ->
                              let uu____3838 =
                                let uu____3839 =
                                  let uu____3840 =
                                    let uu____3841 =
                                      let uu____3842 =
                                        FStar_Syntax_Syntax.bv_to_name
                                          (FStar_Pervasives_Native.fst b) in
                                      FStar_Syntax_Syntax.as_arg uu____3842 in
                                    [uu____3841] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.t_haseq uu____3840 in
                                uu____3839 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange in
                              FStar_Syntax_Util.mk_conj t3 uu____3838)
                         FStar_Syntax_Util.t_true bs' in
                     let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                     let fml1 =
                       let uu___344_3849 = fml in
                       let uu____3850 =
                         let uu____3851 =
                           let uu____3858 =
                             let uu____3859 =
                               let uu____3870 =
                                 let uu____3873 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____3873] in
                               [uu____3870] in
                             FStar_Syntax_Syntax.Meta_pattern uu____3859 in
                           (fml, uu____3858) in
                         FStar_Syntax_Syntax.Tm_meta uu____3851 in
                       {
                         FStar_Syntax_Syntax.n = uu____3850;
                         FStar_Syntax_Syntax.pos =
                           (uu___344_3849.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___344_3849.FStar_Syntax_Syntax.vars)
                       } in
                     let fml2 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____3886 =
                                let uu____3887 =
                                  let uu____3888 =
                                    let uu____3889 =
                                      let uu____3890 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____3890
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____3889 in
                                  [uu____3888] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____3887 in
                              uu____3886 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) ibs1 fml1 in
                     let fml3 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____3915 =
                                let uu____3916 =
                                  let uu____3917 =
                                    let uu____3918 =
                                      let uu____3919 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____3919
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____3918 in
                                  [uu____3917] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____3916 in
                              uu____3915 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) bs2 fml2 in
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
                     let uu____3939 = acc in
                     (match uu____3939 with
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
                                     (uu____4001,uu____4002,uu____4003,t_lid,uu____4005,uu____4006)
                                     -> t_lid = lid
                                 | uu____4011 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4018 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs2 in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4018)
                              FStar_Syntax_Util.t_true t_datas in
                          let axiom_lid =
                            FStar_Ident.lid_of_ids
                              (FStar_List.append lid.FStar_Ident.ns
                                 [FStar_Ident.id_of_text
                                    (Prims.strcat
                                       (lid.FStar_Ident.ident).FStar_Ident.idText
                                       "_haseq")]) in
                          let uu____4020 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____4023 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml3)]),
                            env2, uu____4020, uu____4023)))
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
                  (uu____4106,us,uu____4108,uu____4109,uu____4110,uu____4111)
                  -> us
              | uu____4120 -> failwith "Impossible!" in
            let uu____4121 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____4121 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____4146 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____4146 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____4204 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____4204 with
                       | (phi1,uu____4212) ->
                           ((let uu____4214 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____4214
                             then
                               let uu____4215 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4215
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____4232  ->
                                      match uu____4232 with
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
                let uu____4284 =
                  let uu____4285 = FStar_Syntax_Subst.compress t in
                  uu____4285.FStar_Syntax_Syntax.n in
                match uu____4284 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4292) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4325 = is_mutual t' in
                    if uu____4325
                    then true
                    else
                      (let uu____4327 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4327)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4343) -> is_mutual t'
                | uu____4348 -> false
              and exists_mutual uu___336_4349 =
                match uu___336_4349 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4368 =
                let uu____4369 = FStar_Syntax_Subst.compress dt1 in
                uu____4369.FStar_Syntax_Syntax.n in
              match uu____4368 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4375) ->
                  let dbs1 =
                    let uu____4399 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4399 in
                  let dbs2 =
                    let uu____4437 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4437 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4455 =
                               let uu____4456 =
                                 let uu____4457 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4457] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4456 in
                             uu____4455 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4461 = is_mutual sort in
                             if uu____4461
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____4471 =
                             let uu____4472 =
                               let uu____4473 =
                                 let uu____4474 =
                                   let uu____4475 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4475 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4474 in
                               [uu____4473] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4472 in
                           uu____4471 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4492 -> acc
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
              let uu____4529 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4551,bs,t,uu____4554,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4566 -> failwith "Impossible!" in
              match uu____4529 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____4589 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____4589 t in
                  let uu____4596 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____4596 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4612 =
                           let uu____4613 = FStar_Syntax_Subst.compress t2 in
                           uu____4613.FStar_Syntax_Syntax.n in
                         match uu____4612 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4623) ->
                             ibs
                         | uu____4640 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____4647 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____4648 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4647
                           uu____4648 in
                       let ind1 =
                         let uu____4654 =
                           let uu____4655 =
                             FStar_List.map
                               (fun uu____4668  ->
                                  match uu____4668 with
                                  | (bv,aq) ->
                                      let uu____4679 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4679, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4655 in
                         uu____4654 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____4685 =
                           let uu____4686 =
                             FStar_List.map
                               (fun uu____4699  ->
                                  match uu____4699 with
                                  | (bv,aq) ->
                                      let uu____4710 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4710, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4686 in
                         uu____4685 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____4716 =
                           let uu____4717 =
                             let uu____4718 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____4718] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4717 in
                         uu____4716 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4732,uu____4733,uu____4734,t_lid,uu____4736,uu____4737)
                                  -> t_lid = lid
                              | uu____4742 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___345_4748 = fml in
                         let uu____4749 =
                           let uu____4750 =
                             let uu____4757 =
                               let uu____4758 =
                                 let uu____4769 =
                                   let uu____4772 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____4772] in
                                 [uu____4769] in
                               FStar_Syntax_Syntax.Meta_pattern uu____4758 in
                             (fml, uu____4757) in
                           FStar_Syntax_Syntax.Tm_meta uu____4750 in
                         {
                           FStar_Syntax_Syntax.n = uu____4749;
                           FStar_Syntax_Syntax.pos =
                             (uu___345_4748.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___345_4748.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4785 =
                                  let uu____4786 =
                                    let uu____4787 =
                                      let uu____4788 =
                                        let uu____4789 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4789
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4788 in
                                    [uu____4787] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4786 in
                                uu____4785 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4814 =
                                  let uu____4815 =
                                    let uu____4816 =
                                      let uu____4817 =
                                        let uu____4818 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4818
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4817 in
                                    [uu____4816] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4815 in
                                uu____4814 FStar_Pervasives_Native.None
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
                       (lid,uu____4903,uu____4904,uu____4905,uu____4906,uu____4907)
                       -> lid
                   | uu____4916 -> failwith "Impossible!") tcs in
            let uu____4917 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____4929,uu____4930,uu____4931,uu____4932) ->
                  (lid, us)
              | uu____4941 -> failwith "Impossible!" in
            match uu____4917 with
            | (lid,us) ->
                let uu____4950 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____4950 with
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
                         let uu____4977 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____4977 fml []
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
          let uu____5023 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___337_5048  ->
                    match uu___337_5048 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5049;
                        FStar_Syntax_Syntax.sigrng = uu____5050;
                        FStar_Syntax_Syntax.sigquals = uu____5051;
                        FStar_Syntax_Syntax.sigmeta = uu____5052;
                        FStar_Syntax_Syntax.sigattrs = uu____5053;_} -> true
                    | uu____5074 -> false)) in
          match uu____5023 with
          | (tys,datas) ->
              ((let uu____5096 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___338_5105  ->
                          match uu___338_5105 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5106;
                              FStar_Syntax_Syntax.sigrng = uu____5107;
                              FStar_Syntax_Syntax.sigquals = uu____5108;
                              FStar_Syntax_Syntax.sigmeta = uu____5109;
                              FStar_Syntax_Syntax.sigattrs = uu____5110;_} ->
                              false
                          | uu____5129 -> true)) in
                if uu____5096
                then
                  let uu____5130 =
                    let uu____5131 =
                      let uu____5136 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____5136) in
                    FStar_Errors.Error uu____5131 in
                  FStar_Exn.raise uu____5130
                else ());
               (let env0 = env in
                let uu____5139 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____5178  ->
                         match uu____5178 with
                         | (env1,all_tcs,g) ->
                             let uu____5218 = tc_tycon env1 tc in
                             (match uu____5218 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____5245 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____5245
                                    then
                                      let uu____5246 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____5246
                                    else ());
                                   (let uu____5248 =
                                      let uu____5249 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____5249 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____5248))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____5139 with
                | (env1,tcs,g) ->
                    let uu____5295 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____5317  ->
                             match uu____5317 with
                             | (datas1,g1) ->
                                 let uu____5336 =
                                   let uu____5341 = tc_data env1 tcs in
                                   uu____5341 se in
                                 (match uu____5336 with
                                  | (data,g') ->
                                      let uu____5356 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____5356))) datas
                        ([], g) in
                    (match uu____5295 with
                     | (datas1,g1) ->
                         let uu____5377 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____5377 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____5407 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____5408 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____5407;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____5408
                                } in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs1,binders,typ,uu____5434,uu____5435)
                                           ->
                                           let fail expected inferred =
                                             let uu____5451 =
                                               let uu____5452 =
                                                 let uu____5457 =
                                                   let uu____5458 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       expected in
                                                   let uu____5459 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       inferred in
                                                   FStar_Util.format2
                                                     "Expected an inductive with type %s; got %s"
                                                     uu____5458 uu____5459 in
                                                 (uu____5457,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____5452 in
                                             FStar_Exn.raise uu____5451 in
                                           let uu____5460 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l in
                                           (match uu____5460 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____5476) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____5497 ->
                                                        let uu____5498 =
                                                          let uu____5501 =
                                                            let uu____5502 =
                                                              let uu____5515
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ in
                                                              (binders,
                                                                uu____5515) in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____5502 in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____5501 in
                                                        uu____5498
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
                                                  let uu____5521 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ in
                                                  (match uu____5521 with
                                                   | (uu____5526,inferred) ->
                                                       let uu____5528 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1 in
                                                       (match uu____5528 with
                                                        | (uu____5533,expected)
                                                            ->
                                                            let uu____5535 =
                                                              FStar_TypeChecker_Rel.teq_nosmt
                                                                env0 inferred
                                                                expected in
                                                            if uu____5535
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail expected_typ1
                                                    inferred_typ)
                                       | uu____5538 -> ()));
                               (sig_bndle, tcs1, datas2))))))