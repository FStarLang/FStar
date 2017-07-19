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
          let uu____48 = FStar_Syntax_Subst.open_term tps k in
          (match uu____48 with
           | (tps1,k1) ->
               let uu____63 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____63 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____85 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____85 with
                     | (indices,t) ->
                         let uu____130 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____130 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____151 =
                                let uu____156 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____156 with
                                | (t1,uu____168,g) ->
                                    let uu____170 =
                                      let uu____171 =
                                        let uu____172 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____172 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____171 in
                                    (t1, uu____170) in
                              (match uu____151 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____188 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____188 in
                                   let uu____193 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____193 with
                                    | (t_type,u) ->
                                        ((let uu____209 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____209);
                                         (let t_tc =
                                            let uu____215 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____215 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____227 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____227,
                                            (let uu___84_234 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___84_234.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___84_234.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___84_234.FStar_Syntax_Syntax.sigmeta)
                                             }), u, guard)))))))))
      | uu____241 -> failwith "impossible"
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
            let uu____298 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____324  ->
                     match uu____324 with
                     | (se1,u_tc) ->
                         let uu____339 =
                           let uu____340 =
                             let uu____341 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____341 in
                           FStar_Ident.lid_equals tc_lid uu____340 in
                         if uu____339
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____360,uu____361,tps,uu____363,uu____364,uu____365)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____401  ->
                                          match uu____401 with
                                          | (x,uu____413) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____417 =
                                  let uu____424 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____424, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____417
                            | uu____431 -> failwith "Impossible")
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
            (match uu____298 with
             | (env1,tps,u_tc) ->
                 let uu____502 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____518 =
                     let uu____519 = FStar_Syntax_Subst.compress t1 in
                     uu____519.FStar_Syntax_Syntax.n in
                   match uu____518 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____560 = FStar_Util.first_N ntps bs in
                       (match uu____560 with
                        | (uu____595,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____646  ->
                                        match uu____646 with
                                        | (x,uu____652) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____653 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____653)
                   | uu____654 -> ([], t1) in
                 (match uu____502 with
                  | (arguments,result) ->
                      ((let uu____692 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____692
                        then
                          let uu____693 = FStar_Syntax_Print.lid_to_string c in
                          let uu____694 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____695 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____693
                            uu____694 uu____695
                        else ());
                       (let uu____697 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____697 with
                        | (arguments1,env',us) ->
                            let uu____711 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____711 with
                             | (result1,res_lcomp) ->
                                 ((let uu____723 =
                                     let uu____724 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____724.FStar_Syntax_Syntax.n in
                                   match uu____723 with
                                   | FStar_Syntax_Syntax.Tm_type uu____729 ->
                                       ()
                                   | ty ->
                                       let uu____731 =
                                         let uu____732 =
                                           let uu____737 =
                                             let uu____738 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____739 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____738 uu____739 in
                                           (uu____737,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____732 in
                                       raise uu____731);
                                  (let uu____740 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____740 with
                                   | (head1,uu____764) ->
                                       ((let uu____794 =
                                           let uu____795 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____795.FStar_Syntax_Syntax.n in
                                         match uu____794 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____801 ->
                                             let uu____802 =
                                               let uu____803 =
                                                 let uu____808 =
                                                   let uu____809 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____810 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____809 uu____810 in
                                                 (uu____808,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____803 in
                                             raise uu____802);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____817  ->
                                                  fun u_x  ->
                                                    match uu____817 with
                                                    | (x,uu____824) ->
                                                        let uu____825 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____825)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____831 =
                                             let uu____838 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____865  ->
                                                       match uu____865 with
                                                       | (x,uu____877) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____838
                                               arguments1 in
                                           let uu____886 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____831
                                             uu____886 in
                                         ((let uu___85_891 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___85_891.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___85_891.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___85_891.FStar_Syntax_Syntax.sigmeta)
                                           }), g))))))))))
        | uu____900 -> failwith "impossible"
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
            let uu___86_957 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___86_957.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___86_957.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___86_957.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____967 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____967
           then
             let uu____968 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____968
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____986  ->
                     match uu____986 with
                     | (se,uu____992) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____993,uu____994,tps,k,uu____997,uu____998)
                              ->
                              let uu____1007 =
                                let uu____1008 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1008 in
                              FStar_Syntax_Syntax.null_binder uu____1007
                          | uu____1021 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1030,uu____1031,t,uu____1033,uu____1034,uu____1035)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1040 -> failwith "Impossible")) in
           let t =
             let uu____1046 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1046 in
           (let uu____1052 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____1052
            then
              let uu____1053 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1053
            else ());
           (let uu____1055 =
              FStar_TypeChecker_Util.generalize_universes env t in
            match uu____1055 with
            | (uvs,t1) ->
                ((let uu____1071 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____1071
                  then
                    let uu____1072 =
                      let uu____1073 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____1073
                        (FStar_String.concat ", ") in
                    let uu____1083 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1072 uu____1083
                  else ());
                 (let uu____1085 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____1085 with
                  | (uvs1,t2) ->
                      let uu____1100 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____1100 with
                       | (args,uu____1124) ->
                           let uu____1145 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____1145 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1211  ->
                                       fun uu____1212  ->
                                         match (uu____1211, uu____1212) with
                                         | ((x,uu____1230),(se,uu____1232))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1242,tps,uu____1244,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____1256 =
                                                    let uu____1271 =
                                                      let uu____1272 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____1272.FStar_Syntax_Syntax.n in
                                                    match uu____1271 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1313 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____1313
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1391
                                                                   ->
                                                                   let uu____1398
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____1398
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____1423 -> ([], ty) in
                                                  (match uu____1256 with
                                                   | (tps1,t3) ->
                                                       let uu___87_1456 = se in
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
                                                           (uu___87_1456.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___87_1456.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___87_1456.FStar_Syntax_Syntax.sigmeta)
                                                       })
                                              | uu____1471 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1477 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_29  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_29)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___80_1508  ->
                                                match uu___80_1508 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1516,uu____1517,uu____1518,uu____1519,uu____1520);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1521;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1522;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1523;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1536 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1547  ->
                                           fun d  ->
                                             match uu____1547 with
                                             | (t3,uu____1554) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1556,uu____1557,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1566 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1566
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___88_1567 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___88_1567.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___88_1567.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___88_1567.FStar_Syntax_Syntax.sigmeta)
                                                      }
                                                  | uu____1570 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1581 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1581
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1589 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1589
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1603 =
      let uu____1604 = FStar_Syntax_Subst.compress t in
      uu____1604.FStar_Syntax_Syntax.n in
    match uu____1603 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1631 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1636 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1661 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1684  ->
               match uu____1684 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1720 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1720 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1661
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1849 =
             let uu____1850 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1850 in
           debug_log env uu____1849);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1853 =
              let uu____1854 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1854 in
            debug_log env uu____1853);
           (let uu____1855 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1855) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1857 =
                  let uu____1858 = FStar_Syntax_Subst.compress btype1 in
                  uu____1858.FStar_Syntax_Syntax.n in
                match uu____1857 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1893 = try_get_fv t in
                    (match uu____1893 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1909  ->
                                 match uu____1909 with
                                 | (t1,uu____1915) ->
                                     let uu____1916 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1916) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1946 =
                        let uu____1947 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1947 in
                      if uu____1946
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1955  ->
                               match uu____1955 with
                               | (b,uu____1961) ->
                                   let uu____1962 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1962) sbs)
                           &&
                           ((let uu____1963 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1963 with
                             | (uu____1968,return_type) ->
                                 let uu____1970 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1970)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1971 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1973 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1976) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1987) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1997,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2064  ->
                          match uu____2064 with
                          | (p,uu____2078,t) ->
                              let bs =
                                let uu____2095 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2095 in
                              let uu____2098 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____2098 with
                               | (bs1,t1) ->
                                   let uu____2105 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2105)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2107,uu____2108)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2166 ->
                    ((let uu____2168 =
                        let uu____2169 =
                          let uu____2170 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____2171 =
                            let uu____2172 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____2172 in
                          Prims.strcat uu____2170 uu____2171 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2169 in
                      debug_log env uu____2168);
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
              (let uu____2180 =
                 let uu____2181 =
                   let uu____2182 =
                     let uu____2183 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____2183 in
                   Prims.strcat ilid.FStar_Ident.str uu____2182 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2181 in
               debug_log env uu____2180);
              (let uu____2184 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____2184 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____2199 =
                        already_unfolded ilid args unfolded env in
                      if uu____2199
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____2204 =
                            let uu____2205 =
                              let uu____2206 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____2206
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2205 in
                          debug_log env uu____2204);
                         (let uu____2208 =
                            let uu____2209 = FStar_ST.read unfolded in
                            let uu____2216 =
                              let uu____2223 =
                                let uu____2238 =
                                  let uu____2249 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____2249 in
                                (ilid, uu____2238) in
                              [uu____2223] in
                            FStar_List.append uu____2209 uu____2216 in
                          FStar_ST.write unfolded uu____2208);
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
                  (let uu____2354 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____2354 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u''
                                     (FStar_Pervasives_Native.Some u)
                               | uu____2371 ->
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
                         (let uu____2374 =
                            let uu____2375 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____2375 in
                          debug_log env uu____2374);
                         (let uu____2376 =
                            let uu____2377 = FStar_Syntax_Subst.compress dt1 in
                            uu____2377.FStar_Syntax_Syntax.n in
                          match uu____2376 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____2405 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____2405 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____2454 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____2454 dbs1 in
                                    let c1 =
                                      let uu____2458 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____2458 c in
                                    let uu____2461 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____2461 with
                                     | (args1,uu____2495) ->
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
                                           let uu____2580 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____2580 c1 in
                                         ((let uu____2588 =
                                             let uu____2589 =
                                               let uu____2590 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____2591 =
                                                 let uu____2592 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____2592 in
                                               Prims.strcat uu____2590
                                                 uu____2591 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____2589 in
                                           debug_log env uu____2588);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____2593 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____2595 =
                                  let uu____2596 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____2596.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____2595
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
                   (let uu____2638 = try_get_fv t1 in
                    match uu____2638 with
                    | (fv,uu____2644) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____2673 =
                      let uu____2674 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____2674 in
                    debug_log env uu____2673);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____2676 =
                      FStar_List.fold_left
                        (fun uu____2689  ->
                           fun b  ->
                             match uu____2689 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____2710 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____2711 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____2710, uu____2711))) (true, env)
                        sbs1 in
                    match uu____2676 with | (b,uu____2721) -> b))
              | uu____2722 ->
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
              let uu____2741 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____2741 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u''
                                (FStar_Pervasives_Native.Some u)
                          | uu____2758 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____2760 =
                      let uu____2761 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____2761 in
                    debug_log env uu____2760);
                   (let uu____2762 =
                      let uu____2763 = FStar_Syntax_Subst.compress dt in
                      uu____2763.FStar_Syntax_Syntax.n in
                    match uu____2762 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____2768 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2771) ->
                        let dbs1 =
                          let uu____2799 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____2799 in
                        let dbs2 =
                          let uu____2837 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____2837 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____2842 =
                            let uu____2843 =
                              let uu____2844 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____2844 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____2843 in
                          debug_log env uu____2842);
                         (let uu____2849 =
                            FStar_List.fold_left
                              (fun uu____2862  ->
                                 fun b  ->
                                   match uu____2862 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____2883 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____2884 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____2883, uu____2884)))
                              (true, env) dbs3 in
                          match uu____2849 with | (b,uu____2894) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____2895,uu____2896) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____2926 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____2952 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____2968,uu____2969,uu____2970) -> (lid, us, bs)
        | uu____2979 -> failwith "Impossible!" in
      match uu____2952 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____2989 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____2989 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____3012 =
                 let uu____3015 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____3015 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____3025 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____3025
                      unfolded_inductives env2) uu____3012)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3032,uu____3033,t,uu____3035,uu____3036,uu____3037) -> t
    | uu____3042 -> failwith "Impossible!"
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
          let uu____3061 =
            let uu____3062 = FStar_Syntax_Subst.compress dt1 in
            uu____3062.FStar_Syntax_Syntax.n in
          match uu____3061 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3068) ->
              let dbs1 =
                let uu____3096 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____3096 in
              let dbs2 =
                let uu____3134 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____3134 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____3146 =
                           let uu____3147 =
                             let uu____3148 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____3148] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____3147 in
                         uu____3146 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____3153 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____3153 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____3158 =
                       let uu____3159 =
                         let uu____3160 =
                           let uu____3161 =
                             let uu____3162 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____3162
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____3161 in
                         [uu____3160] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____3159 in
                     uu____3158 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____3189 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____3277 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3299,bs,t,uu____3302,d_lids) -> (lid, bs, t, d_lids)
    | uu____3314 -> failwith "Impossible!" in
  match uu____3277 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____3357 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____3357 t in
      let uu____3364 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____3364 with
       | (bs2,t2) ->
           let ibs =
             let uu____3400 =
               let uu____3401 = FStar_Syntax_Subst.compress t2 in
               uu____3401.FStar_Syntax_Syntax.n in
             match uu____3400 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3413) -> ibs
             | uu____3434 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____3441 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____3442 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____3441 uu____3442 in
           let ind1 =
             let uu____3449 =
               let uu____3450 =
                 FStar_List.map
                   (fun uu____3459  ->
                      match uu____3459 with
                      | (bv,aq) ->
                          let uu____3470 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3470, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____3450 in
             uu____3449 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____3478 =
               let uu____3479 =
                 FStar_List.map
                   (fun uu____3488  ->
                      match uu____3488 with
                      | (bv,aq) ->
                          let uu____3499 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3499, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3479 in
             uu____3478 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____3507 =
               let uu____3508 =
                 let uu____3509 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____3509] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____3508 in
             uu____3507 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____3528 = acc in
                  match uu____3528 with
                  | (uu____3543,en,uu____3545,uu____3546) ->
                      let opt =
                        let uu____3562 =
                          let uu____3563 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____3563 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                          uu____3562 false in
                      (match opt with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some uu____3568 -> true))
               bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____3572 =
                      let uu____3573 =
                        let uu____3574 =
                          let uu____3575 =
                            let uu____3576 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst b) in
                            FStar_Syntax_Syntax.as_arg uu____3576 in
                          [uu____3575] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____3574 in
                      uu____3573 FStar_Pervasives_Native.None
                        FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____3572)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___89_3585 = fml in
             let uu____3586 =
               let uu____3587 =
                 let uu____3596 =
                   let uu____3597 =
                     let uu____3610 =
                       let uu____3613 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3613] in
                     [uu____3610] in
                   FStar_Syntax_Syntax.Meta_pattern uu____3597 in
                 (fml, uu____3596) in
               FStar_Syntax_Syntax.Tm_meta uu____3587 in
             {
               FStar_Syntax_Syntax.n = uu____3586;
               FStar_Syntax_Syntax.tk = (uu___89_3585.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___89_3585.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___89_3585.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3623 =
                      let uu____3624 =
                        let uu____3625 =
                          let uu____3626 =
                            let uu____3627 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3627
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3626 in
                        [uu____3625] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3624 in
                    uu____3623 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3659 =
                      let uu____3660 =
                        let uu____3661 =
                          let uu____3662 =
                            let uu____3663 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3663
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3662 in
                        [uu____3661] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3660 in
                    uu____3659 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____3695 = acc in
           (match uu____3695 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____3754,uu____3755,uu____3756,t_lid,uu____3758,uu____3759)
                           -> t_lid = lid
                       | uu____3764 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____3768 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____3768)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____3770 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____3775 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____3770, uu____3775)))
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
                  (uu____3864,us,uu____3866,uu____3867,uu____3868,uu____3869)
                  -> us
              | uu____3878 -> failwith "Impossible!" in
            let uu____3879 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____3879 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____3904 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____3904 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____3962 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____3962 with
                       | (phi1,uu____3970) ->
                           ((let uu____3972 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____3972
                             then
                               let uu____3973 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____3973
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____3985  ->
                                      match uu____3985 with
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
                let uu____4041 =
                  let uu____4042 = FStar_Syntax_Subst.compress t in
                  uu____4042.FStar_Syntax_Syntax.n in
                match uu____4041 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____4054) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____4103 = is_mutual t' in
                    if uu____4103
                    then true
                    else
                      (let uu____4105 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____4105)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____4129) -> is_mutual t'
                | uu____4138 -> false
              and exists_mutual uu___81_4139 =
                match uu___81_4139 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____4168 =
                let uu____4169 = FStar_Syntax_Subst.compress dt1 in
                uu____4169.FStar_Syntax_Syntax.n in
              match uu____4168 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4179) ->
                  let dbs1 =
                    let uu____4207 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____4207 in
                  let dbs2 =
                    let uu____4245 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____4245 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____4262 =
                               let uu____4263 =
                                 let uu____4264 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____4264] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____4263 in
                             uu____4262 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____4268 = is_mutual sort in
                             if uu____4268
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____4275 =
                             let uu____4276 =
                               let uu____4277 =
                                 let uu____4278 =
                                   let uu____4279 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____4279 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____4278 in
                               [uu____4277] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____4276 in
                           uu____4275 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____4306 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____4359 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____4381,bs,t,uu____4384,d_lids) -> (lid, bs, t, d_lids)
    | uu____4396 -> failwith "Impossible!" in
  match uu____4359 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____4421 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____4421 t in
      let uu____4428 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____4428 with
       | (bs2,t2) ->
           let ibs =
             let uu____4446 =
               let uu____4447 = FStar_Syntax_Subst.compress t2 in
               uu____4447.FStar_Syntax_Syntax.n in
             match uu____4446 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4459) -> ibs
             | uu____4480 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____4487 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____4488 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____4487 uu____4488 in
           let ind1 =
             let uu____4495 =
               let uu____4496 =
                 FStar_List.map
                   (fun uu____4505  ->
                      match uu____4505 with
                      | (bv,aq) ->
                          let uu____4516 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____4516, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____4496 in
             uu____4495 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____4524 =
               let uu____4525 =
                 FStar_List.map
                   (fun uu____4534  ->
                      match uu____4534 with
                      | (bv,aq) ->
                          let uu____4545 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____4545, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4525 in
             uu____4524 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____4553 =
               let uu____4554 =
                 let uu____4555 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____4555] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____4554 in
             uu____4553 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____4562,uu____4563,uu____4564,t_lid,uu____4566,uu____4567)
                      -> t_lid = lid
                  | uu____4572 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___90_4580 = fml in
             let uu____4581 =
               let uu____4582 =
                 let uu____4591 =
                   let uu____4592 =
                     let uu____4605 =
                       let uu____4608 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____4608] in
                     [uu____4605] in
                   FStar_Syntax_Syntax.Meta_pattern uu____4592 in
                 (fml, uu____4591) in
               FStar_Syntax_Syntax.Tm_meta uu____4582 in
             {
               FStar_Syntax_Syntax.n = uu____4581;
               FStar_Syntax_Syntax.tk = (uu___90_4580.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___90_4580.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___90_4580.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____4618 =
                      let uu____4619 =
                        let uu____4620 =
                          let uu____4621 =
                            let uu____4622 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____4622
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____4621 in
                        [uu____4620] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____4619 in
                    uu____4618 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____4654 =
                      let uu____4655 =
                        let uu____4656 =
                          let uu____4657 =
                            let uu____4658 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____4658
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____4657 in
                        [uu____4656] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____4655 in
                    uu____4654 FStar_Pervasives_Native.None
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
                       (lid,uu____4746,uu____4747,uu____4748,uu____4749,uu____4750)
                       -> lid
                   | uu____4759 -> failwith "Impossible!") tcs in
            let uu____4760 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____4772,uu____4773,uu____4774,uu____4775) ->
                  (lid, us)
              | uu____4784 -> failwith "Impossible!" in
            match uu____4760 with
            | (lid,us) ->
                let uu____4793 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____4793 with
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
                         let uu____4820 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____4820 fml []
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
          let uu____4866 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___82_4885  ->
                    match uu___82_4885 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____4886;
                        FStar_Syntax_Syntax.sigrng = uu____4887;
                        FStar_Syntax_Syntax.sigquals = uu____4888;
                        FStar_Syntax_Syntax.sigmeta = uu____4889;_} -> true
                    | uu____4908 -> false)) in
          match uu____4866 with
          | (tys,datas) ->
              ((let uu____4930 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___83_4933  ->
                          match uu___83_4933 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____4934;
                              FStar_Syntax_Syntax.sigrng = uu____4935;
                              FStar_Syntax_Syntax.sigquals = uu____4936;
                              FStar_Syntax_Syntax.sigmeta = uu____4937;_} ->
                              false
                          | uu____4954 -> true)) in
                if uu____4930
                then
                  let uu____4955 =
                    let uu____4956 =
                      let uu____4961 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____4961) in
                    FStar_Errors.Error uu____4956 in
                  raise uu____4955
                else ());
               (let env0 = env in
                let uu____4964 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____4990  ->
                         match uu____4990 with
                         | (env1,all_tcs,g) ->
                             let uu____5030 = tc_tycon env1 tc in
                             (match uu____5030 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____5057 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____5057
                                    then
                                      let uu____5058 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____5058
                                    else ());
                                   (let uu____5060 =
                                      let uu____5061 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____5061 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____5060))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____4964 with
                | (env1,tcs,g) ->
                    let uu____5107 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____5121  ->
                             match uu____5121 with
                             | (datas1,g1) ->
                                 let uu____5140 =
                                   let uu____5145 = tc_data env1 tcs in
                                   uu____5145 se in
                                 (match uu____5140 with
                                  | (data,g') ->
                                      let uu____5160 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____5160))) datas
                        ([], g) in
                    (match uu____5107 with
                     | (datas1,g1) ->
                         let uu____5181 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____5181 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____5211 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____5211;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (sig_bndle, tcs1, datas2)))))