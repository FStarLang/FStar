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
          let uu____42 = FStar_Syntax_Subst.open_term tps k in
          (match uu____42 with
           | (tps1,k1) ->
               let uu____57 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____57 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____79 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____79 with
                     | (indices,t) ->
                         let uu____124 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____124 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____145 =
                                let uu____150 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____150 with
                                | (t1,uu____162,g) ->
                                    let uu____164 =
                                      let uu____165 =
                                        let uu____166 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____166 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____165 in
                                    (t1, uu____164) in
                              (match uu____145 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____182 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____182 in
                                   let uu____187 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____187 with
                                    | (t_type,u) ->
                                        ((let uu____203 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____203);
                                         (let t_tc =
                                            let uu____209 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____209 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____221 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____221,
                                            (let uu___86_229 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___86_229.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___86_229.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___86_229.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___86_229.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____236 -> failwith "impossible"
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
            let uu____295 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____334  ->
                     match uu____334 with
                     | (se1,u_tc) ->
                         let uu____349 =
                           let uu____350 =
                             let uu____351 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____351 in
                           FStar_Ident.lid_equals tc_lid uu____350 in
                         if uu____349
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____370,uu____371,tps,uu____373,uu____374,uu____375)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____414  ->
                                          match uu____414 with
                                          | (x,uu____426) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____430 =
                                  let uu____437 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____437, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____430
                            | uu____444 -> failwith "Impossible")
                         else FStar_Pervasives_Native.None) in
              match tps_u_opt with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng))) in
            (match uu____295 with
             | (env1,tps,u_tc) ->
                 let uu____515 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____531 =
                     let uu____532 = FStar_Syntax_Subst.compress t1 in
                     uu____532.FStar_Syntax_Syntax.n in
                   match uu____531 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____573 = FStar_Util.first_N ntps bs in
                       (match uu____573 with
                        | (uu____608,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____663  ->
                                        match uu____663 with
                                        | (x,uu____669) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____670 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____670)
                   | uu____671 -> ([], t1) in
                 (match uu____515 with
                  | (arguments,result) ->
                      ((let uu____709 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____709
                        then
                          let uu____710 = FStar_Syntax_Print.lid_to_string c in
                          let uu____711 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____712 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____710
                            uu____711 uu____712
                        else ());
                       (let uu____714 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____714 with
                        | (arguments1,env',us) ->
                            let uu____728 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____728 with
                             | (result1,res_lcomp) ->
                                 ((let uu____740 =
                                     let uu____741 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____741.FStar_Syntax_Syntax.n in
                                   match uu____740 with
                                   | FStar_Syntax_Syntax.Tm_type uu____746 ->
                                       ()
                                   | ty ->
                                       let uu____748 =
                                         let uu____749 =
                                           let uu____754 =
                                             let uu____755 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____756 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____755 uu____756 in
                                           (uu____754,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____749 in
                                       raise uu____748);
                                  (let uu____757 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____757 with
                                   | (head1,uu____781) ->
                                       ((let uu____811 =
                                           let uu____812 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____812.FStar_Syntax_Syntax.n in
                                         match uu____811 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____818 ->
                                             let uu____819 =
                                               let uu____820 =
                                                 let uu____825 =
                                                   let uu____826 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____827 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____826 uu____827 in
                                                 (uu____825,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____820 in
                                             raise uu____819);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____840  ->
                                                  fun u_x  ->
                                                    match uu____840 with
                                                    | (x,uu____847) ->
                                                        let uu____848 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____848)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____854 =
                                             let uu____861 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____891  ->
                                                       match uu____891 with
                                                       | (x,uu____903) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____861
                                               arguments1 in
                                           let uu____912 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____854
                                             uu____912 in
                                         ((let uu___87_918 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___87_918.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___87_918.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___87_918.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___87_918.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____927 -> failwith "impossible"
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
            let uu___88_988 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_988.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_988.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_988.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____998 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____998
           then
             let uu____999 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____999
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1027  ->
                     match uu____1027 with
                     | (se,uu____1033) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1034,uu____1035,tps,k,uu____1038,uu____1039)
                              ->
                              let uu____1048 =
                                let uu____1049 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1049 in
                              FStar_Syntax_Syntax.null_binder uu____1048
                          | uu____1062 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1078,uu____1079,t,uu____1081,uu____1082,uu____1083)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1088 -> failwith "Impossible")) in
           let t =
             let uu____1094 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1094 in
           (let uu____1100 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1100
            then
              let uu____1101 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1101
            else ());
           (let uu____1103 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1103 with
            | (uvs,t1) ->
                ((let uu____1119 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1119
                  then
                    let uu____1120 =
                      let uu____1121 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1121
                        (FStar_String.concat ", ") in
                    let uu____1132 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1120 uu____1132
                  else ());
                 (let uu____1134 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1134 with
                  | (uvs1,t2) ->
                      let uu____1149 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1149 with
                       | (args,uu____1173) ->
                           let uu____1194 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1194 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1277  ->
                                       fun uu____1278  ->
                                         match (uu____1277, uu____1278) with
                                         | ((x,uu____1296),(se,uu____1298))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1308,tps,uu____1310,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1322 =
                                                    let uu____1337 =
                                                      let uu____1338 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1338.FStar_Syntax_Syntax.n in
                                                    match uu____1337 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1379 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1379
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1457
                                                                   ->
                                                                   let uu____1464
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____1464
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1489 -> ([], ty) in
                                                  (match uu____1322 with
                                                   | (tps1,t3) ->
                                                       let uu___89_1522 = se in
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
                                                           (uu___89_1522.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___89_1522.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___89_1522.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___89_1522.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1537 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1543 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_39  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_39)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_1585  ->
                                                match uu___82_1585 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1593,uu____1594,uu____1595,uu____1596,uu____1597);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1598;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1599;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1600;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1601;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1616 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1639  ->
                                           fun d  ->
                                             match uu____1639 with
                                             | (t3,uu____1646) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1648,uu____1649,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1658 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1658
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___90_1659 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_1659.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___90_1659.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___90_1659.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___90_1659.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1662 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1675 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1675
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1685 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1685
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1700 =
      let uu____1701 = FStar_Syntax_Subst.compress t in
      uu____1701.FStar_Syntax_Syntax.n in
    match uu____1700 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1728 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1733 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let already_unfolded:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1762 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1788  ->
               match uu____1788 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1825 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1825 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1762
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1957 =
             let uu____1958 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1958 in
           debug_log env uu____1957);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1961 =
              let uu____1962 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1962 in
            debug_log env uu____1961);
           (let uu____1965 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1965) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1975 =
                  let uu____1976 = FStar_Syntax_Subst.compress btype1 in
                  uu____1976.FStar_Syntax_Syntax.n in
                match uu____1975 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2011 = try_get_fv t in
                    (match uu____2011 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2027  ->
                                 match uu____2027 with
                                 | (t1,uu____2033) ->
                                     let uu____2034 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2034) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2060 =
                        let uu____2061 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2061 in
                      if uu____2060
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2073  ->
                               match uu____2073 with
                               | (b,uu____2079) ->
                                   let uu____2080 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2080) sbs)
                           &&
                           ((let uu____2085 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2085 with
                             | (uu____2090,return_type) ->
                                 let uu____2092 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2092)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2093 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2095 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2098) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2109) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2119,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2191  ->
                          match uu____2191 with
                          | (p,uu____2205,t) ->
                              let bs =
                                let uu____2222 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2222 in
                              let uu____2225 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2225 with
                               | (bs1,t1) ->
                                   let uu____2232 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2232)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2234,uu____2235)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2293 ->
                    ((let uu____2295 =
                        let uu____2296 =
                          let uu____2297 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2298 =
                            let uu____2299 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2299 in
                          Prims.strcat uu____2297 uu____2298 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2296 in
                      debug_log env uu____2295);
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
              (let uu____2307 =
                 let uu____2308 =
                   let uu____2309 =
                     let uu____2310 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2310 in
                   Prims.strcat ilid.FStar_Ident.str uu____2309 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2308 in
               debug_log env uu____2307);
              (let uu____2311 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2311 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2326 =
                        already_unfolded ilid args unfolded env in
                      if uu____2326
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2331 =
                            let uu____2332 =
                              let uu____2333 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2333
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2332 in
                          debug_log env uu____2331);
                         (let uu____2335 =
                            let uu____2336 = FStar_ST.read unfolded in
                            let uu____2343 =
                              let uu____2350 =
                                let uu____2365 =
                                  let uu____2376 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2376 in
                                (ilid, uu____2365) in
                              [uu____2350] in
                            FStar_List.append uu____2336 uu____2343 in
                          FStar_ST.write unfolded uu____2335);
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
                  (let uu____2482 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2482 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2504 ->
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
                         (let uu____2507 =
                            let uu____2508 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2508 in
                          debug_log env uu____2507);
                         (let uu____2509 =
                            let uu____2510 = FStar_Syntax_Subst.compress dt1 in
                            uu____2510.FStar_Syntax_Syntax.n in
                          match uu____2509 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2538 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2538 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2587 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2587 dbs1 in
                                    let c1 =
                                      let uu____2591 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2591 c in
                                    let uu____2594 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2594 with
                                     | (args1,uu____2628) ->
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
                                           let uu____2716 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2716 c1 in
                                         ((let uu____2724 =
                                             let uu____2725 =
                                               let uu____2726 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2727 =
                                                 let uu____2728 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2728 in
                                               Prims.strcat uu____2726
                                                 uu____2727 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2725 in
                                           debug_log env uu____2724);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2729 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2731 =
                                  let uu____2732 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2732.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2731
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
                   (let uu____2774 = try_get_fv t1 in
                    match uu____2774 with
                    | (fv,uu____2780) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____2805 =
                      let uu____2806 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2806 in
                    debug_log env uu____2805);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____2808 =
                      FStar_List.fold_left
                        (fun uu____2825  ->
                           fun b  ->
                             match uu____2825 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____2846 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____2847 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____2846, uu____2847))) (true, env)
                        sbs1 in
                    match uu____2808 with | (b,uu____2857) -> b))
              | uu____2858 ->
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
              let uu____2883 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____2883 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____2905 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____2907 =
                      let uu____2908 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____2908 in
                    debug_log env uu____2907);
                   (let uu____2909 =
                      let uu____2910 = FStar_Syntax_Subst.compress dt in
                      uu____2910.FStar_Syntax_Syntax.n in
                    match uu____2909 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____2915 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2918) ->
                        let dbs1 =
                          let uu____2946 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____2946 in
                        let dbs2 =
                          let uu____2984 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____2984 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____2989 =
                            let uu____2990 =
                              let uu____2991 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____2991 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____2990 in
                          debug_log env uu____2989);
                         (let uu____2996 =
                            FStar_List.fold_left
                              (fun uu____3013  ->
                                 fun b  ->
                                   match uu____3013 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3034 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3035 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3034, uu____3035)))
                              (true, env) dbs3 in
                          match uu____2996 with | (b,uu____3045) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3046,uu____3047) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____3077 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3105 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3121,uu____3122,uu____3123) -> (lid, us, bs)
        | uu____3132 -> failwith "Impossible!" in
      match uu____3105 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3142 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3142 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3165 =
                 let uu____3168 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3168 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3180 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3180
                      unfolded_inductives env2) uu____3165)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3189,uu____3190,t,uu____3192,uu____3193,uu____3194) -> t
    | uu____3199 -> failwith "Impossible!"
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
          let uu____3222 =
            let uu____3223 = FStar_Syntax_Subst.compress dt1 in
            uu____3223.FStar_Syntax_Syntax.n in
          match uu____3222 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3229) ->
              let dbs1 =
                let uu____3257 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3257 in
              let dbs2 =
                let uu____3295 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3295 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3312 =
                           let uu____3313 =
                             let uu____3314 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3314] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3313 in
                         uu____3312 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3319 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3319 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3327 =
                       let uu____3328 =
                         let uu____3329 =
                           let uu____3330 =
                             let uu____3331 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3331
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3330 in
                         [uu____3329] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3328 in
                     uu____3327 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3348 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____3443 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3465,bs,t,uu____3468,d_lids) -> (lid, bs, t, d_lids)
    | uu____3480 -> failwith "Impossible!" in
  match uu____3443 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____3523 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____3523 t in
      let uu____3530 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____3530 with
       | (bs2,t2) ->
           let ibs =
             let uu____3566 =
               let uu____3567 = FStar_Syntax_Subst.compress t2 in
               uu____3567.FStar_Syntax_Syntax.n in
             match uu____3566 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3579) -> ibs
             | uu____3600 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____3607 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____3608 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____3607 uu____3608 in
           let ind1 =
             let uu____3616 =
               let uu____3617 =
                 FStar_List.map
                   (fun uu____3630  ->
                      match uu____3630 with
                      | (bv,aq) ->
                          let uu____3641 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3641, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____3617 in
             uu____3616 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____3649 =
               let uu____3650 =
                 FStar_List.map
                   (fun uu____3663  ->
                      match uu____3663 with
                      | (bv,aq) ->
                          let uu____3674 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3674, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3650 in
             uu____3649 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____3682 =
               let uu____3683 =
                 let uu____3684 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____3684] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____3683 in
             uu____3682 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____3710 = acc in
                  match uu____3710 with
                  | (uu____3725,en,uu____3727,uu____3728) ->
                      let opt =
                        let uu____3744 =
                          let uu____3745 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____3745 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                          uu____3744 false in
                      (match opt with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some uu____3750 -> true))
               bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____3757 =
                      let uu____3758 =
                        let uu____3759 =
                          let uu____3760 =
                            let uu____3761 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst b) in
                            FStar_Syntax_Syntax.as_arg uu____3761 in
                          [uu____3760] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____3759 in
                      uu____3758 FStar_Pervasives_Native.None
                        FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____3757)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___91_3770 = fml in
             let uu____3771 =
               let uu____3772 =
                 let uu____3781 =
                   let uu____3782 =
                     let uu____3795 =
                       let uu____3798 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3798] in
                     [uu____3795] in
                   FStar_Syntax_Syntax.Meta_pattern uu____3782 in
                 (fml, uu____3781) in
               FStar_Syntax_Syntax.Tm_meta uu____3772 in
             {
               FStar_Syntax_Syntax.n = uu____3771;
               FStar_Syntax_Syntax.tk = (uu___91_3770.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___91_3770.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___91_3770.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3811 =
                      let uu____3812 =
                        let uu____3813 =
                          let uu____3814 =
                            let uu____3815 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3815
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3814 in
                        [uu____3813] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3812 in
                    uu____3811 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3840 =
                      let uu____3841 =
                        let uu____3842 =
                          let uu____3843 =
                            let uu____3844 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3844
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3843 in
                        [uu____3842] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3841 in
                    uu____3840 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____3866 = acc in
           (match uu____3866 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____3932,uu____3933,uu____3934,t_lid,uu____3936,uu____3937)
                           -> t_lid = lid
                       | uu____3942 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____3949 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____3949)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____3951 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____3956 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____3951, uu____3956)))
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
                  (uu____4050,us,uu____4052,uu____4053,uu____4054,uu____4055)
                  -> us
              | uu____4064 -> failwith "Impossible!" in
            let uu____4065 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____4065 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____4090 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____4090 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____4148 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____4148 with
                       | (phi1,uu____4156) ->
                           ((let uu____4158 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____4158
                             then
                               let uu____4159 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4159
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____4176  ->
                                      match uu____4176 with
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
              (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                FStar_Syntax_Syntax.syntax
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____4238 =
                  let uu____4239 = FStar_Syntax_Subst.compress t in
                  uu____4239.FStar_Syntax_Syntax.n in
                match uu____4238 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4248) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4297 = is_mutual t' in
                    if uu____4297
                    then true
                    else
                      (let uu____4299 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4299)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4323) -> is_mutual t'
                | uu____4332 -> false
              and exists_mutual uu___83_4333 =
                match uu___83_4333 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4362 =
                let uu____4363 = FStar_Syntax_Subst.compress dt1 in
                uu____4363.FStar_Syntax_Syntax.n in
              match uu____4362 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4373) ->
                  let dbs1 =
                    let uu____4401 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4401 in
                  let dbs2 =
                    let uu____4439 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4439 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4461 =
                               let uu____4462 =
                                 let uu____4463 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4463] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4462 in
                             uu____4461 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4467 = is_mutual sort in
                             if uu____4467
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____4477 =
                             let uu____4478 =
                               let uu____4479 =
                                 let uu____4480 =
                                   let uu____4481 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4481 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4480 in
                               [uu____4479] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4478 in
                           uu____4477 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4498 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____4558 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4580,bs,t,uu____4583,d_lids) -> (lid, bs, t, d_lids)
    | uu____4595 -> failwith "Impossible!" in
  match uu____4558 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____4620 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____4620 t in
      let uu____4627 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____4627 with
       | (bs2,t2) ->
           let ibs =
             let uu____4645 =
               let uu____4646 = FStar_Syntax_Subst.compress t2 in
               uu____4646.FStar_Syntax_Syntax.n in
             match uu____4645 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4658) -> ibs
             | uu____4679 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____4686 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____4687 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____4686 uu____4687 in
           let ind1 =
             let uu____4695 =
               let uu____4696 =
                 FStar_List.map
                   (fun uu____4709  ->
                      match uu____4709 with
                      | (bv,aq) ->
                          let uu____4720 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____4720, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____4696 in
             uu____4695 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____4728 =
               let uu____4729 =
                 FStar_List.map
                   (fun uu____4742  ->
                      match uu____4742 with
                      | (bv,aq) ->
                          let uu____4753 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____4753, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4729 in
             uu____4728 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____4761 =
               let uu____4762 =
                 let uu____4763 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____4763] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____4762 in
             uu____4761 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____4777,uu____4778,uu____4779,t_lid,uu____4781,uu____4782)
                      -> t_lid = lid
                  | uu____4787 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___92_4795 = fml in
             let uu____4796 =
               let uu____4797 =
                 let uu____4806 =
                   let uu____4807 =
                     let uu____4820 =
                       let uu____4823 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____4823] in
                     [uu____4820] in
                   FStar_Syntax_Syntax.Meta_pattern uu____4807 in
                 (fml, uu____4806) in
               FStar_Syntax_Syntax.Tm_meta uu____4797 in
             {
               FStar_Syntax_Syntax.n = uu____4796;
               FStar_Syntax_Syntax.tk = (uu___92_4795.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___92_4795.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___92_4795.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____4836 =
                      let uu____4837 =
                        let uu____4838 =
                          let uu____4839 =
                            let uu____4840 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____4840
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____4839 in
                        [uu____4838] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____4837 in
                    uu____4836 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____4865 =
                      let uu____4866 =
                        let uu____4867 =
                          let uu____4868 =
                            let uu____4869 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____4869
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____4868 in
                        [uu____4867] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____4866 in
                    uu____4865 FStar_Pervasives_Native.None
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
                       (lid,uu____4959,uu____4960,uu____4961,uu____4962,uu____4963)
                       -> lid
                   | uu____4972 -> failwith "Impossible!") tcs in
            let uu____4973 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____4985,uu____4986,uu____4987,uu____4988) ->
                  (lid, us)
              | uu____4997 -> failwith "Impossible!" in
            match uu____4973 with
            | (lid,us) ->
                let uu____5006 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____5006 with
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
                         let uu____5033 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____5033 fml []
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
          let uu____5083 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_5108  ->
                    match uu___84_5108 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5109;
                        FStar_Syntax_Syntax.sigrng = uu____5110;
                        FStar_Syntax_Syntax.sigquals = uu____5111;
                        FStar_Syntax_Syntax.sigmeta = uu____5112;
                        FStar_Syntax_Syntax.sigattrs = uu____5113;_} -> true
                    | uu____5134 -> false)) in
          match uu____5083 with
          | (tys,datas) ->
              ((let uu____5156 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_5165  ->
                          match uu___85_5165 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5166;
                              FStar_Syntax_Syntax.sigrng = uu____5167;
                              FStar_Syntax_Syntax.sigquals = uu____5168;
                              FStar_Syntax_Syntax.sigmeta = uu____5169;
                              FStar_Syntax_Syntax.sigattrs = uu____5170;_} ->
                              false
                          | uu____5189 -> true)) in
                if uu____5156
                then
                  let uu____5190 =
                    let uu____5191 =
                      let uu____5196 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____5196) in
                    FStar_Errors.Error uu____5191 in
                  raise uu____5190
                else ());
               (let env0 = env in
                let uu____5199 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____5238  ->
                         match uu____5238 with
                         | (env1,all_tcs,g) ->
                             let uu____5278 = tc_tycon env1 tc in
                             (match uu____5278 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____5305 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____5305
                                    then
                                      let uu____5306 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____5306
                                    else ());
                                   (let uu____5308 =
                                      let uu____5309 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____5309 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____5308))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____5199 with
                | (env1,tcs,g) ->
                    let uu____5355 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____5377  ->
                             match uu____5377 with
                             | (datas1,g1) ->
                                 let uu____5396 =
                                   let uu____5401 = tc_data env1 tcs in
                                   uu____5401 se in
                                 (match uu____5396 with
                                  | (data,g') ->
                                      let uu____5416 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____5416))) datas
                        ([], g) in
                    (match uu____5355 with
                     | (datas1,g1) ->
                         let uu____5437 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____5437 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____5467 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____5468 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____5467;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____5468
                                } in
                              (sig_bndle, tcs1, datas2)))))