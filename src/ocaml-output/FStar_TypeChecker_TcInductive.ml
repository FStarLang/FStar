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
          let uu____29 = FStar_Syntax_Subst.open_term tps k in
          (match uu____29 with
           | (tps1,k1) ->
               let uu____38 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____38 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____52 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____52 with
                     | (indices,t) ->
                         let uu____76 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____76 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____89 =
                                let uu____92 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____92 with
                                | (t1,uu____99,g) ->
                                    let uu____101 =
                                      let uu____102 =
                                        let uu____103 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____103 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____102 in
                                    (t1, uu____101) in
                              (match uu____89 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____113 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____113 in
                                   let uu____116 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____116 with
                                    | (t_type,u) ->
                                        ((let uu____126 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____126);
                                         (let t_tc =
                                            let uu____130 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____130 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____138 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____138,
                                            (let uu___86_143 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____147 -> failwith "impossible"
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
            let uu____187 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____214  ->
                     match uu____214 with
                     | (se1,u_tc) ->
                         let uu____223 =
                           let uu____224 =
                             let uu____225 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____225 in
                           FStar_Ident.lid_equals tc_lid uu____224 in
                         if uu____223
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____235,uu____236,tps,uu____238,uu____239,uu____240)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____262  ->
                                          match uu____262 with
                                          | (x,uu____269) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____272 =
                                  let uu____276 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____276, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____272
                            | uu____280 -> failwith "Impossible")
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
            (match uu____187 with
             | (env1,tps,u_tc) ->
                 let uu____319 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____328 =
                     let uu____329 = FStar_Syntax_Subst.compress t1 in
                     uu____329.FStar_Syntax_Syntax.n in
                   match uu____328 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____351 = FStar_Util.first_N ntps bs in
                       (match uu____351 with
                        | (uu____369,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____405  ->
                                        match uu____405 with
                                        | (x,uu____409) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____410 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____410)
                   | uu____411 -> ([], t1) in
                 (match uu____319 with
                  | (arguments,result) ->
                      ((let uu____432 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____432
                        then
                          let uu____433 = FStar_Syntax_Print.lid_to_string c in
                          let uu____434 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____435 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____433
                            uu____434 uu____435
                        else ());
                       (let uu____437 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____437 with
                        | (arguments1,env',us) ->
                            let uu____446 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____446 with
                             | (result1,res_lcomp) ->
                                 ((let uu____454 =
                                     let uu____455 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____455.FStar_Syntax_Syntax.n in
                                   match uu____454 with
                                   | FStar_Syntax_Syntax.Tm_type uu____458 ->
                                       ()
                                   | ty ->
                                       let uu____460 =
                                         let uu____461 =
                                           let uu____464 =
                                             let uu____465 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____466 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____465 uu____466 in
                                           (uu____464,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____461 in
                                       raise uu____460);
                                  (let uu____467 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____467 with
                                   | (head1,uu____480) ->
                                       ((let uu____496 =
                                           let uu____497 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____497.FStar_Syntax_Syntax.n in
                                         match uu____496 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____501 ->
                                             let uu____502 =
                                               let uu____503 =
                                                 let uu____506 =
                                                   let uu____507 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____508 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____507 uu____508 in
                                                 (uu____506,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____503 in
                                             raise uu____502);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____519  ->
                                                  fun u_x  ->
                                                    match uu____519 with
                                                    | (x,uu____524) ->
                                                        let uu____525 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____525)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____529 =
                                             let uu____533 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____550  ->
                                                       match uu____550 with
                                                       | (x,uu____557) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____533
                                               arguments1 in
                                           let uu____562 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____529
                                             uu____562 in
                                         ((let uu___87_566 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___87_566.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___87_566.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___87_566.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___87_566.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____571 -> failwith "impossible"
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
            let uu___88_611 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_611.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_611.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_611.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____617 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____617
           then
             let uu____618 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____618
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____639  ->
                     match uu____639 with
                     | (se,uu____643) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____644,uu____645,tps,k,uu____648,uu____649)
                              ->
                              let uu____654 =
                                let uu____655 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____655 in
                              FStar_Syntax_Syntax.null_binder uu____654
                          | uu____662 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____675,uu____676,t,uu____678,uu____679,uu____680)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____683 -> failwith "Impossible")) in
           let t =
             let uu____687 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____687 in
           (let uu____691 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____691
            then
              let uu____692 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____692
            else ());
           (let uu____694 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____694 with
            | (uvs,t1) ->
                ((let uu____704 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____704
                  then
                    let uu____705 =
                      let uu____706 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____706
                        (FStar_String.concat ", ") in
                    let uu____713 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____705 uu____713
                  else ());
                 (let uu____715 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____715 with
                  | (uvs1,t2) ->
                      let uu____724 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____724 with
                       | (args,uu____737) ->
                           let uu____748 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____748 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____804  ->
                                       fun uu____805  ->
                                         match (uu____804, uu____805) with
                                         | ((x,uu____815),(se,uu____817)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____823,tps,uu____825,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____833 =
                                                    let uu____841 =
                                                      let uu____842 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____842.FStar_Syntax_Syntax.n in
                                                    match uu____841 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____864 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____864 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____909 ->
                                                                   let uu____913
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____913
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____932 -> ([], ty) in
                                                  (match uu____833 with
                                                   | (tps1,t3) ->
                                                       let uu___89_950 = se in
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
                                                           (uu___89_950.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___89_950.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___89_950.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___89_950.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____958 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____962 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_39  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_39)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_990  ->
                                                match uu___82_990 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____995,uu____996,uu____997,uu____998,uu____999);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1000;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1001;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1002;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1003;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1011 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1029  ->
                                           fun d  ->
                                             match uu____1029 with
                                             | (t3,uu____1034) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1036,uu____1037,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1044 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1044
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___90_1045 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_1045.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___90_1045.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___90_1045.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___90_1045.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1047 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1058 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1058
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1068 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1068
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1078 =
      let uu____1079 = FStar_Syntax_Subst.compress t in
      uu____1079.FStar_Syntax_Syntax.n in
    match uu____1078 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1095 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1098 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1121 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1136  ->
               match uu____1136 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1157 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1157 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1121
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1257 =
             let uu____1258 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1258 in
           debug_log env uu____1257);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1261 =
              let uu____1262 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1262 in
            debug_log env uu____1261);
           (let uu____1265 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1265) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1275 =
                  let uu____1276 = FStar_Syntax_Subst.compress btype1 in
                  uu____1276.FStar_Syntax_Syntax.n in
                match uu____1275 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1295 = try_get_fv t in
                    (match uu____1295 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1307  ->
                                 match uu____1307 with
                                 | (t1,uu____1311) ->
                                     let uu____1312 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1312) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1328 =
                        let uu____1329 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1329 in
                      if uu____1328
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1339  ->
                               match uu____1339 with
                               | (b,uu____1343) ->
                                   let uu____1344 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1344) sbs)
                           &&
                           ((let uu____1349 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1349 with
                             | (uu____1352,return_type) ->
                                 let uu____1354 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1354)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1355 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1357 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1360) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1367) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1373,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1415  ->
                          match uu____1415 with
                          | (p,uu____1423,t) ->
                              let bs =
                                let uu____1433 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1433 in
                              let uu____1435 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1435 with
                               | (bs1,t1) ->
                                   let uu____1440 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1440)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1442,uu____1443)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1473 ->
                    ((let uu____1475 =
                        let uu____1476 =
                          let uu____1477 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____1478 =
                            let uu____1479 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____1479 in
                          Prims.strcat uu____1477 uu____1478 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1476 in
                      debug_log env uu____1475);
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
              (let uu____1487 =
                 let uu____1488 =
                   let uu____1489 =
                     let uu____1490 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1490 in
                   Prims.strcat ilid.FStar_Ident.str uu____1489 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1488 in
               debug_log env uu____1487);
              (let uu____1491 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1491 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1501 =
                        already_unfolded ilid args unfolded env in
                      if uu____1501
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1506 =
                            let uu____1507 =
                              let uu____1508 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1508
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1507 in
                          debug_log env uu____1506);
                         (let uu____1510 =
                            let uu____1511 = FStar_ST.read unfolded in
                            let uu____1515 =
                              let uu____1519 =
                                let uu____1527 =
                                  let uu____1533 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____1533 in
                                (ilid, uu____1527) in
                              [uu____1519] in
                            FStar_List.append uu____1511 uu____1515 in
                          FStar_ST.write unfolded uu____1510);
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
                  (let uu____1592 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1592 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____1608 ->
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
                         (let uu____1611 =
                            let uu____1612 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1612 in
                          debug_log env uu____1611);
                         (let uu____1613 =
                            let uu____1614 = FStar_Syntax_Subst.compress dt1 in
                            uu____1614.FStar_Syntax_Syntax.n in
                          match uu____1613 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1630 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1630 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____1657 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1657 dbs1 in
                                    let c1 =
                                      let uu____1660 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1660 c in
                                    let uu____1662 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1662 with
                                     | (args1,uu____1680) ->
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
                                           let uu____1729 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1729 c1 in
                                         ((let uu____1740 =
                                             let uu____1741 =
                                               let uu____1742 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____1743 =
                                                 let uu____1744 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____1744 in
                                               Prims.strcat uu____1742
                                                 uu____1743 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1741 in
                                           debug_log env uu____1740);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1745 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1747 =
                                  let uu____1748 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____1748.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1747
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
                   (let uu____1774 = try_get_fv t1 in
                    match uu____1774 with
                    | (fv,uu____1778) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1793 =
                      let uu____1794 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1794 in
                    debug_log env uu____1793);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____1796 =
                      FStar_List.fold_left
                        (fun uu____1807  ->
                           fun b  ->
                             match uu____1807 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1820 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____1821 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____1820, uu____1821))) (true, env)
                        sbs1 in
                    match uu____1796 with | (b,uu____1827) -> b))
              | uu____1828 ->
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
              let uu____1853 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____1853 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____1869 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1871 =
                      let uu____1872 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1872 in
                    debug_log env uu____1871);
                   (let uu____1873 =
                      let uu____1874 = FStar_Syntax_Subst.compress dt in
                      uu____1874.FStar_Syntax_Syntax.n in
                    match uu____1873 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1877 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1880) ->
                        let dbs1 =
                          let uu____1895 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____1895 in
                        let dbs2 =
                          let uu____1919 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1919 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____1923 =
                            let uu____1924 =
                              let uu____1925 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____1925 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1924 in
                          debug_log env uu____1923);
                         (let uu____1934 =
                            FStar_List.fold_left
                              (fun uu____1945  ->
                                 fun b  ->
                                   match uu____1945 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1958 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____1959 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____1958, uu____1959)))
                              (true, env) dbs3 in
                          match uu____1934 with | (b,uu____1965) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1966,uu____1967) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1983 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____2003 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____2013,uu____2014,uu____2015) -> (lid, us, bs)
        | uu____2020 -> failwith "Impossible!" in
      match uu____2003 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____2027 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____2027 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____2042 =
                 let uu____2044 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____2044 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____2052 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____2052
                      unfolded_inductives env2) uu____2042)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2061,uu____2062,t,uu____2064,uu____2065,uu____2066) -> t
    | uu____2069 -> failwith "Impossible!"
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
          let uu____2090 =
            let uu____2091 = FStar_Syntax_Subst.compress dt1 in
            uu____2091.FStar_Syntax_Syntax.n in
          match uu____2090 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2095) ->
              let dbs1 =
                let uu____2110 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____2110 in
              let dbs2 =
                let uu____2134 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____2134 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____2148 =
                           let uu____2149 =
                             let uu____2150 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____2150] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____2149 in
                         uu____2148 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____2157 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____2157 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2165 =
                       let uu____2166 =
                         let uu____2167 =
                           let uu____2168 =
                             let uu____2169 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____2169
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____2168 in
                         [uu____2167] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2166 in
                     uu____2165 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____2181 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2247 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2259,bs,t,uu____2262,d_lids) -> (lid, bs, t, d_lids)
    | uu____2269 -> failwith "Impossible!" in
  match uu____2247 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2294 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2294 t in
      let uu____2304 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2304 with
       | (bs2,t2) ->
           let ibs =
             let uu____2324 =
               let uu____2325 = FStar_Syntax_Subst.compress t2 in
               uu____2325.FStar_Syntax_Syntax.n in
             match uu____2324 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2332) -> ibs
             | uu____2343 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2348 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____2349 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2348 uu____2349 in
           let ind1 =
             let uu____2355 =
               let uu____2356 =
                 FStar_List.map
                   (fun uu____2365  ->
                      match uu____2365 with
                      | (bv,aq) ->
                          let uu____2372 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2372, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2356 in
             uu____2355 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____2380 =
               let uu____2381 =
                 FStar_List.map
                   (fun uu____2390  ->
                      match uu____2390 with
                      | (bv,aq) ->
                          let uu____2397 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2397, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2381 in
             uu____2380 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2405 =
               let uu____2406 =
                 let uu____2407 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2407] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2406 in
             uu____2405 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2428 = acc in
                  match uu____2428 with
                  | (uu____2436,en,uu____2438,uu____2439) ->
                      let opt =
                        let uu____2448 =
                          let uu____2449 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____2449 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                          uu____2448 false in
                      (match opt with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some uu____2452 -> true))
               bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2459 =
                      let uu____2460 =
                        let uu____2461 =
                          let uu____2462 =
                            let uu____2463 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst b) in
                            FStar_Syntax_Syntax.as_arg uu____2463 in
                          [uu____2462] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2461 in
                      uu____2460 FStar_Pervasives_Native.None
                        FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____2459)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___91_2472 = fml in
             let uu____2473 =
               let uu____2474 =
                 let uu____2479 =
                   let uu____2480 =
                     let uu____2487 =
                       let uu____2489 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2489] in
                     [uu____2487] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2480 in
                 (fml, uu____2479) in
               FStar_Syntax_Syntax.Tm_meta uu____2474 in
             {
               FStar_Syntax_Syntax.n = uu____2473;
               FStar_Syntax_Syntax.tk = (uu___91_2472.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___91_2472.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___91_2472.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2504 =
                      let uu____2505 =
                        let uu____2506 =
                          let uu____2507 =
                            let uu____2508 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____2508
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____2507 in
                        [uu____2506] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2505 in
                    uu____2504 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2528 =
                      let uu____2529 =
                        let uu____2530 =
                          let uu____2531 =
                            let uu____2532 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____2532
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____2531 in
                        [uu____2530] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2529 in
                    uu____2528 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____2547 = acc in
           (match uu____2547 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2588,uu____2589,uu____2590,t_lid,uu____2592,uu____2593)
                           -> t_lid = lid
                       | uu____2596 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2603 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____2603)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____2605 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____2608 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2605, uu____2608)))
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
                  (uu____2679,us,uu____2681,uu____2682,uu____2683,uu____2684)
                  -> us
              | uu____2689 -> failwith "Impossible!" in
            let uu____2690 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2690 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____2706 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2706 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2738 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____2738 with
                       | (phi1,uu____2743) ->
                           ((let uu____2745 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____2745
                             then
                               let uu____2746 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2746
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2759  ->
                                      match uu____2759 with
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
                let uu____2808 =
                  let uu____2809 = FStar_Syntax_Subst.compress t in
                  uu____2809.FStar_Syntax_Syntax.n in
                match uu____2808 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2816) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2843 = is_mutual t' in
                    if uu____2843
                    then true
                    else
                      (let uu____2845 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____2845)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2858) -> is_mutual t'
                | uu____2863 -> false
              and exists_mutual uu___83_2864 =
                match uu___83_2864 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____2881 =
                let uu____2882 = FStar_Syntax_Subst.compress dt1 in
                uu____2882.FStar_Syntax_Syntax.n in
              match uu____2881 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2888) ->
                  let dbs1 =
                    let uu____2903 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____2903 in
                  let dbs2 =
                    let uu____2927 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2927 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2944 =
                               let uu____2945 =
                                 let uu____2946 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2946] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2945 in
                             uu____2944 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____2952 = is_mutual sort in
                             if uu____2952
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2962 =
                             let uu____2963 =
                               let uu____2964 =
                                 let uu____2965 =
                                   let uu____2966 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____2966 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____2965 in
                               [uu____2964] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2963 in
                           uu____2962 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2978 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____3028 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3040,bs,t,uu____3043,d_lids) -> (lid, bs, t, d_lids)
    | uu____3050 -> failwith "Impossible!" in
  match uu____3028 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____3066 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____3066 t in
      let uu____3076 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____3076 with
       | (bs2,t2) ->
           let ibs =
             let uu____3087 =
               let uu____3088 = FStar_Syntax_Subst.compress t2 in
               uu____3088.FStar_Syntax_Syntax.n in
             match uu____3087 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3095) -> ibs
             | uu____3106 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____3111 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____3112 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____3111 uu____3112 in
           let ind1 =
             let uu____3118 =
               let uu____3119 =
                 FStar_List.map
                   (fun uu____3128  ->
                      match uu____3128 with
                      | (bv,aq) ->
                          let uu____3135 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3135, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____3119 in
             uu____3118 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let ind2 =
             let uu____3143 =
               let uu____3144 =
                 FStar_List.map
                   (fun uu____3153  ->
                      match uu____3153 with
                      | (bv,aq) ->
                          let uu____3160 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3160, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3144 in
             uu____3143 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____3168 =
               let uu____3169 =
                 let uu____3170 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____3170] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____3169 in
             uu____3168 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____3185,uu____3186,uu____3187,t_lid,uu____3189,uu____3190)
                      -> t_lid = lid
                  | uu____3193 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___92_3199 = fml in
             let uu____3200 =
               let uu____3201 =
                 let uu____3206 =
                   let uu____3207 =
                     let uu____3214 =
                       let uu____3216 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3216] in
                     [uu____3214] in
                   FStar_Syntax_Syntax.Meta_pattern uu____3207 in
                 (fml, uu____3206) in
               FStar_Syntax_Syntax.Tm_meta uu____3201 in
             {
               FStar_Syntax_Syntax.n = uu____3200;
               FStar_Syntax_Syntax.tk = (uu___92_3199.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___92_3199.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___92_3199.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3231 =
                      let uu____3232 =
                        let uu____3233 =
                          let uu____3234 =
                            let uu____3235 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3235
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3234 in
                        [uu____3233] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3232 in
                    uu____3231 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3255 =
                      let uu____3256 =
                        let uu____3257 =
                          let uu____3258 =
                            let uu____3259 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs
                              [((FStar_Pervasives_Native.fst b),
                                 FStar_Pervasives_Native.None)] uu____3259
                              FStar_Pervasives_Native.None in
                          FStar_Syntax_Syntax.as_arg uu____3258 in
                        [uu____3257] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3256 in
                    uu____3255 FStar_Pervasives_Native.None
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
                       (lid,uu____3335,uu____3336,uu____3337,uu____3338,uu____3339)
                       -> lid
                   | uu____3344 -> failwith "Impossible!") tcs in
            let uu____3345 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3353,uu____3354,uu____3355,uu____3356) ->
                  (lid, us)
              | uu____3361 -> failwith "Impossible!" in
            match uu____3345 with
            | (lid,us) ->
                let uu____3367 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3367 with
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
                         let uu____3385 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____3385 fml []
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
          let uu____3419 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_3435  ->
                    match uu___84_3435 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3436;
                        FStar_Syntax_Syntax.sigrng = uu____3437;
                        FStar_Syntax_Syntax.sigquals = uu____3438;
                        FStar_Syntax_Syntax.sigmeta = uu____3439;
                        FStar_Syntax_Syntax.sigattrs = uu____3440;_} -> true
                    | uu____3451 -> false)) in
          match uu____3419 with
          | (tys,datas) ->
              ((let uu____3464 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_3472  ->
                          match uu___85_3472 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3473;
                              FStar_Syntax_Syntax.sigrng = uu____3474;
                              FStar_Syntax_Syntax.sigquals = uu____3475;
                              FStar_Syntax_Syntax.sigmeta = uu____3476;
                              FStar_Syntax_Syntax.sigattrs = uu____3477;_} ->
                              false
                          | uu____3487 -> true)) in
                if uu____3464
                then
                  let uu____3488 =
                    let uu____3489 =
                      let uu____3492 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3492) in
                    FStar_Errors.Error uu____3489 in
                  raise uu____3488
                else ());
               (let env0 = env in
                let uu____3495 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3522  ->
                         match uu____3522 with
                         | (env1,all_tcs,g) ->
                             let uu____3544 = tc_tycon env1 tc in
                             (match uu____3544 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3561 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____3561
                                    then
                                      let uu____3562 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3562
                                    else ());
                                   (let uu____3564 =
                                      let uu____3565 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3565 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3564))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3495 with
                | (env1,tcs,g) ->
                    let uu____3590 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3606  ->
                             match uu____3606 with
                             | (datas1,g1) ->
                                 let uu____3617 =
                                   let uu____3620 = tc_data env1 tcs in
                                   uu____3620 se in
                                 (match uu____3617 with
                                  | (data,g') ->
                                      let uu____3630 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____3630))) datas
                        ([], g) in
                    (match uu____3590 with
                     | (datas1,g1) ->
                         let uu____3642 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____3642 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3659 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____3660 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3659;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____3660
                                } in
                              (sig_bndle, tcs1, datas2)))))