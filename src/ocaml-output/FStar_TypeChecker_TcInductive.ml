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
                         let uu____118 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____118 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____139 =
                                let uu____144 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____144 with
                                | (t1,uu____156,g) ->
                                    let uu____158 =
                                      let uu____159 =
                                        let uu____160 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____160 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____159 in
                                    (t1, uu____158) in
                              (match uu____139 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____174 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____174 in
                                   let uu____177 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____177 with
                                    | (t_type,u) ->
                                        ((let uu____193 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____193);
                                         (let t_tc =
                                            let uu____197 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____197 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____207 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____207,
                                            (let uu___117_213 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___117_213.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___117_213.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___117_213.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___117_213.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____220 -> failwith "impossible"
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
            let uu____279 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____318  ->
                     match uu____318 with
                     | (se1,u_tc) ->
                         let uu____333 =
                           let uu____334 =
                             let uu____335 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____335 in
                           FStar_Ident.lid_equals tc_lid uu____334 in
                         if uu____333
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____354,uu____355,tps,uu____357,uu____358,uu____359)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____398  ->
                                          match uu____398 with
                                          | (x,uu____410) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____414 =
                                  let uu____421 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____421, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____414
                            | uu____428 -> failwith "Impossible")
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
            (match uu____279 with
             | (env1,tps,u_tc) ->
                 let uu____499 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____513 =
                     let uu____514 = FStar_Syntax_Subst.compress t1 in
                     uu____514.FStar_Syntax_Syntax.n in
                   match uu____513 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____547 = FStar_Util.first_N ntps bs in
                       (match uu____547 with
                        | (uu____580,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____631  ->
                                        match uu____631 with
                                        | (x,uu____637) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____638 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____638)
                   | uu____639 -> ([], t1) in
                 (match uu____499 with
                  | (arguments,result) ->
                      ((let uu____673 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____673
                        then
                          let uu____674 = FStar_Syntax_Print.lid_to_string c in
                          let uu____675 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____676 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____674
                            uu____675 uu____676
                        else ());
                       (let uu____678 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____678 with
                        | (arguments1,env',us) ->
                            let uu____692 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____692 with
                             | (result1,res_lcomp) ->
                                 ((let uu____704 =
                                     let uu____705 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____705.FStar_Syntax_Syntax.n in
                                   match uu____704 with
                                   | FStar_Syntax_Syntax.Tm_type uu____708 ->
                                       ()
                                   | ty ->
                                       let uu____710 =
                                         let uu____711 =
                                           let uu____716 =
                                             let uu____717 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____718 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____717 uu____718 in
                                           (uu____716,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____711 in
                                       FStar_Exn.raise uu____710);
                                  (let uu____719 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____719 with
                                   | (head1,uu____739) ->
                                       ((let uu____761 =
                                           let uu____762 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____762.FStar_Syntax_Syntax.n in
                                         match uu____761 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____766 ->
                                             let uu____767 =
                                               let uu____768 =
                                                 let uu____773 =
                                                   let uu____774 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____775 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____774 uu____775 in
                                                 (uu____773,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____768 in
                                             FStar_Exn.raise uu____767);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____788  ->
                                                  fun u_x  ->
                                                    match uu____788 with
                                                    | (x,uu____795) ->
                                                        let uu____796 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____796)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____800 =
                                             let uu____807 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____837  ->
                                                       match uu____837 with
                                                       | (x,uu____849) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____807
                                               arguments1 in
                                           let uu____858 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____800
                                             uu____858 in
                                         ((let uu___118_862 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___118_862.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___118_862.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___118_862.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___118_862.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____869 -> failwith "impossible"
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
            let uu___119_930 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___119_930.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___119_930.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___119_930.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____940 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____940
           then
             let uu____941 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____941
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____969  ->
                     match uu____969 with
                     | (se,uu____975) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____976,uu____977,tps,k,uu____980,uu____981)
                              ->
                              let uu____990 =
                                let uu____991 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____991 in
                              FStar_Syntax_Syntax.null_binder uu____990
                          | uu____998 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1014,uu____1015,t,uu____1017,uu____1018,uu____1019)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1024 -> failwith "Impossible")) in
           let t =
             let uu____1028 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1028 in
           (let uu____1032 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1032
            then
              let uu____1033 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1033
            else ());
           (let uu____1035 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1035 with
            | (uvs,t1) ->
                ((let uu____1051 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1051
                  then
                    let uu____1052 =
                      let uu____1053 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1053
                        (FStar_String.concat ", ") in
                    let uu____1064 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1052 uu____1064
                  else ());
                 (let uu____1066 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1066 with
                  | (uvs1,t2) ->
                      let uu____1081 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1081 with
                       | (args,uu____1103) ->
                           let uu____1120 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1120 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1203  ->
                                       fun uu____1204  ->
                                         match (uu____1203, uu____1204) with
                                         | ((x,uu____1222),(se,uu____1224))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1234,tps,uu____1236,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1248 =
                                                    let uu____1261 =
                                                      let uu____1262 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1262.FStar_Syntax_Syntax.n in
                                                    match uu____1261 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1295 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1295
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1367
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1390 -> ([], ty) in
                                                  (match uu____1248 with
                                                   | (tps1,t3) ->
                                                       let uu___120_1419 = se in
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
                                                           (uu___120_1419.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___120_1419.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___120_1419.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___120_1419.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1432 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1438 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_40  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_40)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___113_1480  ->
                                                match uu___113_1480 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1488,uu____1489,uu____1490,uu____1491,uu____1492);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1493;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1494;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1495;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1496;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1511 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1534  ->
                                           fun d  ->
                                             match uu____1534 with
                                             | (t3,uu____1541) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1543,uu____1544,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1553 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1553
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___121_1554 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___121_1554.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___121_1554.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___121_1554.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___121_1554.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1557 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1570 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1570
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1580 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1580
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1595 =
      let uu____1596 = FStar_Syntax_Subst.compress t in
      uu____1596.FStar_Syntax_Syntax.n in
    match uu____1595 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1617 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1622 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1663 = FStar_ST.op_Bang unfolded in
          FStar_List.existsML
            (fun uu____1747  ->
               match uu____1747 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1782 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1782 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1663
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1934 =
             let uu____1935 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1935 in
           debug_log env uu____1934);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1938 =
              let uu____1939 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1939 in
            debug_log env uu____1938);
           (let uu____1942 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1942) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1952 =
                  let uu____1953 = FStar_Syntax_Subst.compress btype1 in
                  uu____1953.FStar_Syntax_Syntax.n in
                match uu____1952 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1978 = try_get_fv t in
                    (match uu____1978 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1994  ->
                                 match uu____1994 with
                                 | (t1,uu____2000) ->
                                     let uu____2001 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____2001) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____2035 =
                        let uu____2036 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____2036 in
                      if uu____2035
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____2048  ->
                               match uu____2048 with
                               | (b,uu____2054) ->
                                   let uu____2055 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____2055) sbs)
                           &&
                           ((let uu____2060 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____2060 with
                             | (uu____2065,return_type) ->
                                 let uu____2067 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2067)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2080 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2082 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2085) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2104) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2122,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2180  ->
                          match uu____2180 with
                          | (p,uu____2192,t) ->
                              let bs =
                                let uu____2205 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2205 in
                              let uu____2208 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2208 with
                               | (bs1,t1) ->
                                   let uu____2215 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2215)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2229,uu____2230)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2284 ->
                    ((let uu____2286 =
                        let uu____2287 =
                          let uu____2288 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2289 =
                            let uu____2290 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2290 in
                          Prims.strcat uu____2288 uu____2289 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2287 in
                      debug_log env uu____2286);
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
              (let uu____2304 =
                 let uu____2305 =
                   let uu____2306 =
                     let uu____2307 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2307 in
                   Prims.strcat ilid.FStar_Ident.str uu____2306 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2305 in
               debug_log env uu____2304);
              (let uu____2308 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2308 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2323 =
                        already_unfolded ilid args unfolded env in
                      if uu____2323
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2340 =
                            let uu____2341 =
                              let uu____2342 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2342
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2341 in
                          debug_log env uu____2340);
                         (let uu____2344 =
                            let uu____2345 = FStar_ST.op_Bang unfolded in
                            let uu____2410 =
                              let uu____2417 =
                                let uu____2430 =
                                  let uu____2439 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2439 in
                                (ilid, uu____2430) in
                              [uu____2417] in
                            FStar_List.append uu____2345 uu____2410 in
                          FStar_ST.op_Colon_Equals unfolded uu____2344);
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
                  (let uu____2605 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2605 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____2627 ->
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
                         (let uu____2630 =
                            let uu____2631 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2631 in
                          debug_log env uu____2630);
                         (let uu____2632 =
                            let uu____2633 = FStar_Syntax_Subst.compress dt1 in
                            uu____2633.FStar_Syntax_Syntax.n in
                          match uu____2632 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2655 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2655 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2704 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2704 dbs1 in
                                    let c1 =
                                      let uu____2708 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2708 c in
                                    let uu____2711 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2711 with
                                     | (args1,uu____2739) ->
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
                                           let uu____2811 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2811 c1 in
                                         ((let uu____2819 =
                                             let uu____2820 =
                                               let uu____2821 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2822 =
                                                 let uu____2823 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2823 in
                                               Prims.strcat uu____2821
                                                 uu____2822 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2820 in
                                           debug_log env uu____2819);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2836 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2838 =
                                  let uu____2839 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2839.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2838
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
                   (let uu____2889 = try_get_fv t1 in
                    match uu____2889 with
                    | (fv,uu____2895) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____2916 =
                      let uu____2917 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2917 in
                    debug_log env uu____2916);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____2919 =
                      FStar_List.fold_left
                        (fun uu____2936  ->
                           fun b  ->
                             match uu____2936 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____2957 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____2970 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____2957, uu____2970))) (true, env)
                        sbs1 in
                    match uu____2919 with | (b,uu____2980) -> b))
              | uu____2981 ->
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
              let uu____3018 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____3018 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3040 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3042 =
                      let uu____3043 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____3043 in
                    debug_log env uu____3042);
                   (let uu____3044 =
                      let uu____3045 = FStar_Syntax_Subst.compress dt in
                      uu____3045.FStar_Syntax_Syntax.n in
                    match uu____3044 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3048 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3051) ->
                        let dbs1 =
                          let uu____3075 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____3075 in
                        let dbs2 =
                          let uu____3113 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____3113 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____3118 =
                            let uu____3119 =
                              let uu____3120 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____3120 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3119 in
                          debug_log env uu____3118);
                         (let uu____3125 =
                            FStar_List.fold_left
                              (fun uu____3142  ->
                                 fun b  ->
                                   match uu____3142 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3163 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____3176 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____3163, uu____3176)))
                              (true, env) dbs3 in
                          match uu____3125 with | (b,uu____3186) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3187,uu____3188) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3229 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____3257 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3273,uu____3274,uu____3275) -> (lid, us, bs)
        | uu____3284 -> failwith "Impossible!" in
      match uu____3257 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____3294 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____3294 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3317 =
                 let uu____3320 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3320 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3332 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3332
                      unfolded_inductives env2) uu____3317)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3353,uu____3354,t,uu____3356,uu____3357,uu____3358) -> t
    | uu____3363 -> failwith "Impossible!"
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
          let uu____3386 =
            let uu____3387 = FStar_Syntax_Subst.compress dt1 in
            uu____3387.FStar_Syntax_Syntax.n in
          match uu____3386 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3391) ->
              let dbs1 =
                let uu____3415 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3415 in
              let dbs2 =
                let uu____3453 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3453 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3468 =
                           let uu____3469 =
                             let uu____3470 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3470] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3469 in
                         uu____3468 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3475 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3475 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3483 =
                       let uu____3484 =
                         let uu____3485 =
                           let uu____3486 =
                             let uu____3487 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3487
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3486 in
                         [uu____3485] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3484 in
                     uu____3483 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3504 -> FStar_Syntax_Util.t_true
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
            let uu____3579 =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____3601,bs,t,uu____3604,d_lids) ->
                  (lid, bs, t, d_lids)
              | uu____3616 -> failwith "Impossible!" in
            match uu____3579 with
            | (lid,bs,t,d_lids) ->
                let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                let t1 =
                  let uu____3655 =
                    FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                      usubst in
                  FStar_Syntax_Subst.subst uu____3655 t in
                let uu____3662 = FStar_Syntax_Subst.open_term bs1 t1 in
                (match uu____3662 with
                 | (bs2,t2) ->
                     let ibs =
                       let uu____3694 =
                         let uu____3695 = FStar_Syntax_Subst.compress t2 in
                         uu____3695.FStar_Syntax_Syntax.n in
                       match uu____3694 with
                       | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3705) -> ibs
                       | uu____3722 -> [] in
                     let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                     let ind =
                       let uu____3729 =
                         FStar_Syntax_Syntax.fvar lid
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       let uu____3730 =
                         FStar_List.map
                           (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____3729 uu____3730 in
                     let ind1 =
                       let uu____3736 =
                         let uu____3737 =
                           FStar_List.map
                             (fun uu____3750  ->
                                match uu____3750 with
                                | (bv,aq) ->
                                    let uu____3761 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3761, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____3737 in
                       uu____3736 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let ind2 =
                       let uu____3767 =
                         let uu____3768 =
                           FStar_List.map
                             (fun uu____3781  ->
                                match uu____3781 with
                                | (bv,aq) ->
                                    let uu____3792 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____3792, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3768 in
                       uu____3767 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let haseq_ind =
                       let uu____3798 =
                         let uu____3799 =
                           let uu____3800 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____3800] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____3799 in
                       uu____3798 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let bs' =
                       FStar_List.filter
                         (fun b  ->
                            let uu____3826 = acc in
                            match uu____3826 with
                            | (uu____3841,en,uu____3843,uu____3844) ->
                                let opt =
                                  let uu____3860 =
                                    let uu____3861 =
                                      FStar_Syntax_Util.type_u () in
                                    FStar_Pervasives_Native.fst uu____3861 in
                                  FStar_TypeChecker_Rel.try_subtype' en
                                    (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    uu____3860 false in
                                (match opt with
                                 | FStar_Pervasives_Native.None  -> false
                                 | FStar_Pervasives_Native.Some uu____3866 ->
                                     true)) bs2 in
                     let haseq_bs =
                       FStar_List.fold_left
                         (fun t3  ->
                            fun b  ->
                              let uu____3873 =
                                let uu____3874 =
                                  let uu____3875 =
                                    let uu____3876 =
                                      let uu____3877 =
                                        FStar_Syntax_Syntax.bv_to_name
                                          (FStar_Pervasives_Native.fst b) in
                                      FStar_Syntax_Syntax.as_arg uu____3877 in
                                    [uu____3876] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.t_haseq uu____3875 in
                                uu____3874 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange in
                              FStar_Syntax_Util.mk_conj t3 uu____3873)
                         FStar_Syntax_Util.t_true bs' in
                     let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                     let fml1 =
                       let uu___122_3884 = fml in
                       let uu____3885 =
                         let uu____3886 =
                           let uu____3893 =
                             let uu____3894 =
                               let uu____3905 =
                                 let uu____3908 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____3908] in
                               [uu____3905] in
                             FStar_Syntax_Syntax.Meta_pattern uu____3894 in
                           (fml, uu____3893) in
                         FStar_Syntax_Syntax.Tm_meta uu____3886 in
                       {
                         FStar_Syntax_Syntax.n = uu____3885;
                         FStar_Syntax_Syntax.pos =
                           (uu___122_3884.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___122_3884.FStar_Syntax_Syntax.vars)
                       } in
                     let fml2 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____3921 =
                                let uu____3922 =
                                  let uu____3923 =
                                    let uu____3924 =
                                      let uu____3925 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____3925
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____3924 in
                                  [uu____3923] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____3922 in
                              uu____3921 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) ibs1 fml1 in
                     let fml3 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____3950 =
                                let uu____3951 =
                                  let uu____3952 =
                                    let uu____3953 =
                                      let uu____3954 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____3954
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____3953 in
                                  [uu____3952] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____3951 in
                              uu____3950 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) bs2 fml2 in
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
                     let uu____3974 = acc in
                     (match uu____3974 with
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
                                     (uu____4036,uu____4037,uu____4038,t_lid,uu____4040,uu____4041)
                                     -> t_lid = lid
                                 | uu____4046 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____4053 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs2 in
                                   FStar_Syntax_Util.mk_conj acc1 uu____4053)
                              FStar_Syntax_Util.t_true t_datas in
                          let axiom_lid =
                            FStar_Ident.lid_of_ids
                              (FStar_List.append lid.FStar_Ident.ns
                                 [FStar_Ident.id_of_text
                                    (Prims.strcat
                                       (lid.FStar_Ident.ident).FStar_Ident.idText
                                       "_haseq")]) in
                          let uu____4055 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____4058 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml3)]),
                            env2, uu____4055, uu____4058)))
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
                  (uu____4146,us,uu____4148,uu____4149,uu____4150,uu____4151)
                  -> us
              | uu____4160 -> failwith "Impossible!" in
            let uu____4161 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____4161 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____4186 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____4186 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____4244 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____4244 with
                       | (phi1,uu____4252) ->
                           ((let uu____4254 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____4254
                             then
                               let uu____4255 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____4255
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____4272  ->
                                      match uu____4272 with
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
                let uu____4330 =
                  let uu____4331 = FStar_Syntax_Subst.compress t in
                  uu____4331.FStar_Syntax_Syntax.n in
                match uu____4330 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4338) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4371 = is_mutual t' in
                    if uu____4371
                    then true
                    else
                      (let uu____4373 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4373)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4389) -> is_mutual t'
                | uu____4394 -> false
              and exists_mutual uu___114_4395 =
                match uu___114_4395 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4414 =
                let uu____4415 = FStar_Syntax_Subst.compress dt1 in
                uu____4415.FStar_Syntax_Syntax.n in
              match uu____4414 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4421) ->
                  let dbs1 =
                    let uu____4445 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4445 in
                  let dbs2 =
                    let uu____4483 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4483 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4501 =
                               let uu____4502 =
                                 let uu____4503 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4503] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4502 in
                             uu____4501 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4507 = is_mutual sort in
                             if uu____4507
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____4517 =
                             let uu____4518 =
                               let uu____4519 =
                                 let uu____4520 =
                                   let uu____4521 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4521 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4520 in
                               [uu____4519] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4518 in
                           uu____4517 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4538 -> acc
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
              let uu____4581 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____4603,bs,t,uu____4606,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____4618 -> failwith "Impossible!" in
              match uu____4581 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____4641 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____4641 t in
                  let uu____4648 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____4648 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____4664 =
                           let uu____4665 = FStar_Syntax_Subst.compress t2 in
                           uu____4665.FStar_Syntax_Syntax.n in
                         match uu____4664 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4675) ->
                             ibs
                         | uu____4692 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____4699 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____4700 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____4699
                           uu____4700 in
                       let ind1 =
                         let uu____4706 =
                           let uu____4707 =
                             FStar_List.map
                               (fun uu____4720  ->
                                  match uu____4720 with
                                  | (bv,aq) ->
                                      let uu____4731 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4731, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____4707 in
                         uu____4706 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____4737 =
                           let uu____4738 =
                             FStar_List.map
                               (fun uu____4751  ->
                                  match uu____4751 with
                                  | (bv,aq) ->
                                      let uu____4762 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____4762, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4738 in
                         uu____4737 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____4768 =
                           let uu____4769 =
                             let uu____4770 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____4770] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4769 in
                         uu____4768 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____4784,uu____4785,uu____4786,t_lid,uu____4788,uu____4789)
                                  -> t_lid = lid
                              | uu____4794 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___123_4800 = fml in
                         let uu____4801 =
                           let uu____4802 =
                             let uu____4809 =
                               let uu____4810 =
                                 let uu____4821 =
                                   let uu____4824 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____4824] in
                                 [uu____4821] in
                               FStar_Syntax_Syntax.Meta_pattern uu____4810 in
                             (fml, uu____4809) in
                           FStar_Syntax_Syntax.Tm_meta uu____4802 in
                         {
                           FStar_Syntax_Syntax.n = uu____4801;
                           FStar_Syntax_Syntax.pos =
                             (uu___123_4800.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___123_4800.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4837 =
                                  let uu____4838 =
                                    let uu____4839 =
                                      let uu____4840 =
                                        let uu____4841 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4841
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4840 in
                                    [uu____4839] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4838 in
                                uu____4837 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____4866 =
                                  let uu____4867 =
                                    let uu____4868 =
                                      let uu____4869 =
                                        let uu____4870 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____4870
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____4869 in
                                    [uu____4868] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____4867 in
                                uu____4866 FStar_Pervasives_Native.None
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
                       (lid,uu____4960,uu____4961,uu____4962,uu____4963,uu____4964)
                       -> lid
                   | uu____4973 -> failwith "Impossible!") tcs in
            let uu____4974 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____4986,uu____4987,uu____4988,uu____4989) ->
                  (lid, us)
              | uu____4998 -> failwith "Impossible!" in
            match uu____4974 with
            | (lid,us) ->
                let uu____5007 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____5007 with
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
                         let uu____5034 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____5034 fml []
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
          let uu____5084 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___115_5109  ->
                    match uu___115_5109 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____5110;
                        FStar_Syntax_Syntax.sigrng = uu____5111;
                        FStar_Syntax_Syntax.sigquals = uu____5112;
                        FStar_Syntax_Syntax.sigmeta = uu____5113;
                        FStar_Syntax_Syntax.sigattrs = uu____5114;_} -> true
                    | uu____5135 -> false)) in
          match uu____5084 with
          | (tys,datas) ->
              ((let uu____5157 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___116_5166  ->
                          match uu___116_5166 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____5167;
                              FStar_Syntax_Syntax.sigrng = uu____5168;
                              FStar_Syntax_Syntax.sigquals = uu____5169;
                              FStar_Syntax_Syntax.sigmeta = uu____5170;
                              FStar_Syntax_Syntax.sigattrs = uu____5171;_} ->
                              false
                          | uu____5190 -> true)) in
                if uu____5157
                then
                  let uu____5191 =
                    let uu____5192 =
                      let uu____5197 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____5197) in
                    FStar_Errors.Error uu____5192 in
                  FStar_Exn.raise uu____5191
                else ());
               (let env0 = env in
                let uu____5200 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____5239  ->
                         match uu____5239 with
                         | (env1,all_tcs,g) ->
                             let uu____5279 = tc_tycon env1 tc in
                             (match uu____5279 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____5306 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____5306
                                    then
                                      let uu____5307 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____5307
                                    else ());
                                   (let uu____5309 =
                                      let uu____5310 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____5310 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____5309))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____5200 with
                | (env1,tcs,g) ->
                    let uu____5356 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____5378  ->
                             match uu____5378 with
                             | (datas1,g1) ->
                                 let uu____5397 =
                                   let uu____5402 = tc_data env1 tcs in
                                   uu____5402 se in
                                 (match uu____5397 with
                                  | (data,g') ->
                                      let uu____5417 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____5417))) datas
                        ([], g) in
                    (match uu____5356 with
                     | (datas1,g1) ->
                         let uu____5438 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____5438 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____5468 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____5469 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____5468;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____5469
                                } in
                              (sig_bndle, tcs1, datas2)))))