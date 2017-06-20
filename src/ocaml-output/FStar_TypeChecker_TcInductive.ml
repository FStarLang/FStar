open Prims
let tc_tycon:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t* FStar_Syntax_Syntax.sigelt*
        FStar_Syntax_Syntax.universe* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let uu____27 = FStar_Syntax_Subst.open_term tps k in
          (match uu____27 with
           | (tps1,k1) ->
               let uu____36 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____36 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____50 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____50 with
                     | (indices,t) ->
                         let uu____74 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____74 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____87 =
                                let uu____90 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____90 with
                                | (t1,uu____97,g) ->
                                    let uu____99 =
                                      let uu____100 =
                                        let uu____101 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____101 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____100 in
                                    (t1, uu____99) in
                              (match uu____87 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____111 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____111 in
                                   let uu____114 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____114 with
                                    | (t_type,u) ->
                                        ((let uu____124 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____124);
                                         (let t_tc =
                                            let uu____128 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____128 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None in
                                          let uu____136 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____136,
                                            (let uu___84_141 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___84_141.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___84_141.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___84_141.FStar_Syntax_Syntax.sigmeta)
                                             }), u, guard)))))))))
      | uu____145 -> failwith "impossible"
let tc_data:
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____183 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____210  ->
                     match uu____210 with
                     | (se1,u_tc) ->
                         let uu____219 =
                           let uu____220 =
                             let uu____221 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____221 in
                           FStar_Ident.lid_equals tc_lid uu____220 in
                         if uu____219
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____231,uu____232,tps,uu____234,uu____235,uu____236)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____258  ->
                                          match uu____258 with
                                          | (x,uu____265) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____268 =
                                  let uu____272 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____272, tps2, u_tc) in
                                Some uu____268
                            | uu____276 -> failwith "Impossible")
                         else None) in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng))) in
            (match uu____183 with
             | (env1,tps,u_tc) ->
                 let uu____315 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____324 =
                     let uu____325 = FStar_Syntax_Subst.compress t1 in
                     uu____325.FStar_Syntax_Syntax.n in
                   match uu____324 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____347 = FStar_Util.first_N ntps bs in
                       (match uu____347 with
                        | (uu____365,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                None t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____401  ->
                                        match uu____401 with
                                        | (x,uu____405) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____406 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____406)
                   | uu____407 -> ([], t1) in
                 (match uu____315 with
                  | (arguments,result) ->
                      ((let uu____428 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____428
                        then
                          let uu____429 = FStar_Syntax_Print.lid_to_string c in
                          let uu____430 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____431 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____429
                            uu____430 uu____431
                        else ());
                       (let uu____433 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____433 with
                        | (arguments1,env',us) ->
                            let uu____442 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____442 with
                             | (result1,res_lcomp) ->
                                 ((let uu____450 =
                                     let uu____451 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____451.FStar_Syntax_Syntax.n in
                                   match uu____450 with
                                   | FStar_Syntax_Syntax.Tm_type uu____454 ->
                                       ()
                                   | ty ->
                                       let uu____456 =
                                         let uu____457 =
                                           let uu____460 =
                                             let uu____461 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____462 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____461 uu____462 in
                                           (uu____460,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____457 in
                                       raise uu____456);
                                  (let uu____463 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____463 with
                                   | (head1,uu____476) ->
                                       ((let uu____492 =
                                           let uu____493 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____493.FStar_Syntax_Syntax.n in
                                         match uu____492 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____497 ->
                                             let uu____498 =
                                               let uu____499 =
                                                 let uu____502 =
                                                   let uu____503 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____504 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____503 uu____504 in
                                                 (uu____502,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____499 in
                                             raise uu____498);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____515  ->
                                                  fun u_x  ->
                                                    match uu____515 with
                                                    | (x,uu____520) ->
                                                        let uu____521 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____521)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____525 =
                                             let uu____529 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____546  ->
                                                       match uu____546 with
                                                       | (x,uu____553) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____529
                                               arguments1 in
                                           let uu____558 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____525
                                             uu____558 in
                                         ((let uu___85_562 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___85_562.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___85_562.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___85_562.FStar_Syntax_Syntax.sigmeta)
                                           }), g))))))))))
        | uu____567 -> failwith "impossible"
let generalize_and_inst_within:
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universe) Prims.list
        ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars = FStar_List.map FStar_Pervasives.snd tcs in
          let g1 =
            let uu___86_603 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___86_603.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___86_603.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars, (snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___86_603.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____609 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____609
           then
             let uu____610 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____610
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____631  ->
                     match uu____631 with
                     | (se,uu____635) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____636,uu____637,tps,k,uu____640,uu____641)
                              ->
                              let uu____646 =
                                let uu____647 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____647 in
                              FStar_Syntax_Syntax.null_binder uu____646
                          | uu____654 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____667,uu____668,t,uu____670,uu____671,uu____672)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____675 -> failwith "Impossible")) in
           let t =
             let uu____679 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____679 in
           (let uu____683 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____683
            then
              let uu____684 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____684
            else ());
           (let uu____686 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____686 with
            | (uvs,t1) ->
                ((let uu____696 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____696
                  then
                    let uu____697 =
                      let uu____698 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____698
                        (FStar_String.concat ", ") in
                    let uu____705 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____697 uu____705
                  else ());
                 (let uu____707 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____707 with
                  | (uvs1,t2) ->
                      let uu____716 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____716 with
                       | (args,uu____729) ->
                           let uu____740 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____740 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____794  ->
                                       fun uu____795  ->
                                         match (uu____794, uu____795) with
                                         | ((x,uu____805),(se,uu____807)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____813,tps,uu____815,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____823 =
                                                    let uu____831 =
                                                      let uu____832 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____832.FStar_Syntax_Syntax.n in
                                                    match uu____831 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____854 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____854 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____897 ->
                                                                   let uu____901
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____901
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____920 -> ([], ty) in
                                                  (match uu____823 with
                                                   | (tps1,t3) ->
                                                       let uu___87_938 = se in
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
                                                           (uu___87_938.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___87_938.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___87_938.FStar_Syntax_Syntax.sigmeta)
                                                       })
                                              | uu____946 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____950 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_29  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_29)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___80_977  ->
                                                match uu___80_977 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____982,uu____983,uu____984,uu____985,uu____986);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____987;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____988;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____989;_}
                                                    -> (tc, uvs_universes)
                                                | uu____996 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____1014  ->
                                           fun d  ->
                                             match uu____1014 with
                                             | (t3,uu____1019) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1021,uu____1022,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1029 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____1029
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___88_1030 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___88_1030.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___88_1030.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___88_1030.FStar_Syntax_Syntax.sigmeta)
                                                      }
                                                  | uu____1032 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1041 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1041
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1049 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1049
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv* FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____1058 =
      let uu____1059 = FStar_Syntax_Subst.compress t in
      uu____1059.FStar_Syntax_Syntax.n in
    match uu____1058 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1075 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1078 -> failwith "Node is not an fvar or a Tm_uinst"
type unfolded_memo_elt =
  (FStar_Ident.lident* FStar_Syntax_Syntax.args) Prims.list
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
          let uu____1097 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1112  ->
               match uu____1112 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1133 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        fst uu____1133 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env (
                                    fst a) (fst a'))) true args l))
            uu____1097
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1231 =
             let uu____1232 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1232 in
           debug_log env uu____1231);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1235 =
              let uu____1236 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1236 in
            debug_log env uu____1235);
           (let uu____1239 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1239) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1249 =
                  let uu____1250 = FStar_Syntax_Subst.compress btype1 in
                  uu____1250.FStar_Syntax_Syntax.n in
                match uu____1249 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1269 = try_get_fv t in
                    (match uu____1269 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1281  ->
                                 match uu____1281 with
                                 | (t1,uu____1285) ->
                                     let uu____1286 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1286) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1302 =
                        let uu____1303 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1303 in
                      if uu____1302
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1313  ->
                               match uu____1313 with
                               | (b,uu____1317) ->
                                   let uu____1318 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1318) sbs)
                           &&
                           ((let uu____1323 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1323 with
                             | (uu____1326,return_type) ->
                                 let uu____1328 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1328)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1329 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1331 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1334) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1341) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1347,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1389  ->
                          match uu____1389 with
                          | (p,uu____1397,t) ->
                              let bs =
                                let uu____1407 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1407 in
                              let uu____1409 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1409 with
                               | (bs1,t1) ->
                                   let uu____1414 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1414)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1416,uu____1417)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1447 ->
                    ((let uu____1449 =
                        let uu____1450 =
                          let uu____1451 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____1452 =
                            let uu____1453 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____1453 in
                          Prims.strcat uu____1451 uu____1452 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1450 in
                      debug_log env uu____1449);
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
              (let uu____1461 =
                 let uu____1462 =
                   let uu____1463 =
                     let uu____1464 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1464 in
                   Prims.strcat ilid.FStar_Ident.str uu____1463 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1462 in
               debug_log env uu____1461);
              (let uu____1465 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1465 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1475 =
                        already_unfolded ilid args unfolded env in
                      if uu____1475
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1480 =
                            let uu____1481 =
                              let uu____1482 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1482
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1481 in
                          debug_log env uu____1480);
                         (let uu____1484 =
                            let uu____1485 = FStar_ST.read unfolded in
                            let uu____1489 =
                              let uu____1493 =
                                let uu____1501 =
                                  let uu____1507 =
                                    FStar_List.splitAt num_ibs args in
                                  fst uu____1507 in
                                (ilid, uu____1501) in
                              [uu____1493] in
                            FStar_List.append uu____1485 uu____1489 in
                          FStar_ST.write unfolded uu____1484);
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
                  (let uu____1566 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1566 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____1582 ->
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
                         (let uu____1585 =
                            let uu____1586 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1586 in
                          debug_log env uu____1585);
                         (let uu____1587 =
                            let uu____1588 = FStar_Syntax_Subst.compress dt1 in
                            uu____1588.FStar_Syntax_Syntax.n in
                          match uu____1587 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1604 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1604 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____1631 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1631 dbs1 in
                                    let c1 =
                                      let uu____1634 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1634 c in
                                    let uu____1636 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1636 with
                                     | (args1,uu____1654) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((fst ib),
                                                           (fst arg))]) []
                                             ibs1 args1 in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2 in
                                         let c2 =
                                           let uu____1703 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1703 c1 in
                                         ((let uu____1711 =
                                             let uu____1712 =
                                               let uu____1713 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____1714 =
                                                 let uu____1715 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____1715 in
                                               Prims.strcat uu____1713
                                                 uu____1714 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1712 in
                                           debug_log env uu____1711);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1716 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1718 =
                                  let uu____1719 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____1719.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1718
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
                   (let uu____1745 = try_get_fv t1 in
                    match uu____1745 with
                    | (fv,uu____1749) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1764 =
                      let uu____1765 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1765 in
                    debug_log env uu____1764);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____1767 =
                      FStar_List.fold_left
                        (fun uu____1778  ->
                           fun b  ->
                             match uu____1778 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1791 =
                                      ty_strictly_positive_in_type ty_lid
                                        (fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____1792 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____1791, uu____1792))) (true, env)
                        sbs1 in
                    match uu____1767 with | (b,uu____1798) -> b))
              | uu____1799 ->
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
              let uu____1818 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____1818 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____1834 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1836 =
                      let uu____1837 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1837 in
                    debug_log env uu____1836);
                   (let uu____1838 =
                      let uu____1839 = FStar_Syntax_Subst.compress dt in
                      uu____1839.FStar_Syntax_Syntax.n in
                    match uu____1838 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1842 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1845) ->
                        let dbs1 =
                          let uu____1860 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          snd uu____1860 in
                        let dbs2 =
                          let uu____1882 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1882 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____1886 =
                            let uu____1887 =
                              let uu____1888 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____1888 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1887 in
                          debug_log env uu____1886);
                         (let uu____1894 =
                            FStar_List.fold_left
                              (fun uu____1905  ->
                                 fun b  ->
                                   match uu____1905 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1918 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____1919 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____1918, uu____1919)))
                              (true, env) dbs3 in
                          match uu____1894 with | (b,uu____1925) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1926,uu____1927) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1943 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____1961 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1971,uu____1972,uu____1973) -> (lid, us, bs)
        | uu____1978 -> failwith "Impossible!" in
      match uu____1961 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1985 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____1985 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____2000 =
                 let uu____2002 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 snd uu____2002 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____2010 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____2010
                      unfolded_inductives env2) uu____2000)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2018,uu____2019,t,uu____2021,uu____2022,uu____2023) -> t
    | uu____2026 -> failwith "Impossible!"
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
          let uu____2043 =
            let uu____2044 = FStar_Syntax_Subst.compress dt1 in
            uu____2044.FStar_Syntax_Syntax.n in
          match uu____2043 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2048) ->
              let dbs1 =
                let uu____2063 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                snd uu____2063 in
              let dbs2 =
                let uu____2085 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____2085 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____2099 =
                           let uu____2100 =
                             let uu____2101 =
                               FStar_Syntax_Syntax.as_arg
                                 (fst b).FStar_Syntax_Syntax.sort in
                             [uu____2101] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____2100 in
                         uu____2099 None FStar_Range.dummyRange in
                       let sort_range =
                         ((fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____2108 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____2108 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2116 =
                       let uu____2117 =
                         let uu____2118 =
                           let uu____2119 =
                             let uu____2120 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs [((fst b), None)]
                               uu____2120 None in
                           FStar_Syntax_Syntax.as_arg uu____2119 in
                         [uu____2118] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2117 in
                     uu____2116 None FStar_Range.dummyRange) dbs3 cond
          | uu____2137 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2196 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2208,bs,t,uu____2211,d_lids) -> (lid, bs, t, d_lids)
    | uu____2218 -> failwith "Impossible!" in
  match uu____2196 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2243 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2243 t in
      let uu____2250 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2250 with
       | (bs2,t2) ->
           let ibs =
             let uu____2270 =
               let uu____2271 = FStar_Syntax_Subst.compress t2 in
               uu____2271.FStar_Syntax_Syntax.n in
             match uu____2270 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2278) -> ibs
             | uu____2289 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2294 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2295 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2294 uu____2295 in
           let ind1 =
             let uu____2301 =
               let uu____2302 =
                 FStar_List.map
                   (fun uu____2311  ->
                      match uu____2311 with
                      | (bv,aq) ->
                          let uu____2318 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2318, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2302 in
             uu____2301 None FStar_Range.dummyRange in
           let ind2 =
             let uu____2326 =
               let uu____2327 =
                 FStar_List.map
                   (fun uu____2336  ->
                      match uu____2336 with
                      | (bv,aq) ->
                          let uu____2343 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2343, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2327 in
             uu____2326 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2351 =
               let uu____2352 =
                 let uu____2353 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2353] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2352 in
             uu____2351 None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2374 = acc in
                  match uu____2374 with
                  | (uu____2382,en,uu____2384,uu____2385) ->
                      let opt =
                        let uu____2394 =
                          let uu____2395 = FStar_Syntax_Util.type_u () in
                          fst uu____2395 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (fst b).FStar_Syntax_Syntax.sort uu____2394 false in
                      (match opt with
                       | None  -> false
                       | Some uu____2398 -> true)) bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2405 =
                      let uu____2406 =
                        let uu____2407 =
                          let uu____2408 =
                            let uu____2409 =
                              FStar_Syntax_Syntax.bv_to_name (fst b) in
                            FStar_Syntax_Syntax.as_arg uu____2409 in
                          [uu____2408] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2407 in
                      uu____2406 None FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____2405)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___89_2418 = fml in
             let uu____2419 =
               let uu____2420 =
                 let uu____2425 =
                   let uu____2426 =
                     let uu____2433 =
                       let uu____2435 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2435] in
                     [uu____2433] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2426 in
                 (fml, uu____2425) in
               FStar_Syntax_Syntax.Tm_meta uu____2420 in
             {
               FStar_Syntax_Syntax.n = uu____2419;
               FStar_Syntax_Syntax.tk = (uu___89_2418.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___89_2418.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___89_2418.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2450 =
                      let uu____2451 =
                        let uu____2452 =
                          let uu____2453 =
                            let uu____2454 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2454 None in
                          FStar_Syntax_Syntax.as_arg uu____2453 in
                        [uu____2452] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2451 in
                    uu____2450 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2479 =
                      let uu____2480 =
                        let uu____2481 =
                          let uu____2482 =
                            let uu____2483 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2483 None in
                          FStar_Syntax_Syntax.as_arg uu____2482 in
                        [uu____2481] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2480 in
                    uu____2479 None FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____2503 = acc in
           (match uu____2503 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2544,uu____2545,uu____2546,t_lid,uu____2548,uu____2549)
                           -> t_lid = lid
                       | uu____2552 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2559 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____2559)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____2561 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____2564 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2561, uu____2564)))
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
                  (uu____2630,us,uu____2632,uu____2633,uu____2634,uu____2635)
                  -> us
              | uu____2640 -> failwith "Impossible!" in
            let uu____2641 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2641 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____2657 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2657 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2689 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____2689 with
                       | (phi1,uu____2694) ->
                           ((let uu____2696 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____2696
                             then
                               let uu____2697 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2697
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2710  ->
                                      match uu____2710 with
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
                let uu____2753 =
                  let uu____2754 = FStar_Syntax_Subst.compress t in
                  uu____2754.FStar_Syntax_Syntax.n in
                match uu____2753 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2761) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2788 = is_mutual t' in
                    if uu____2788
                    then true
                    else
                      (let uu____2790 =
                         FStar_List.map FStar_Pervasives.fst args in
                       exists_mutual uu____2790)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2803) -> is_mutual t'
                | uu____2808 -> false
              and exists_mutual uu___81_2809 =
                match uu___81_2809 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____2826 =
                let uu____2827 = FStar_Syntax_Subst.compress dt1 in
                uu____2827.FStar_Syntax_Syntax.n in
              match uu____2826 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2833) ->
                  let dbs1 =
                    let uu____2848 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    snd uu____2848 in
                  let dbs2 =
                    let uu____2870 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2870 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2887 =
                               let uu____2888 =
                                 let uu____2889 =
                                   FStar_Syntax_Syntax.as_arg
                                     (fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2889] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2888 in
                             uu____2887 None FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____2895 = is_mutual sort in
                             if uu____2895
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2905 =
                             let uu____2906 =
                               let uu____2907 =
                                 let uu____2908 =
                                   let uu____2909 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs [((fst b), None)]
                                     uu____2909 None in
                                 FStar_Syntax_Syntax.as_arg uu____2908 in
                               [uu____2907] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2906 in
                           uu____2905 None FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2926 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2969 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2981,bs,t,uu____2984,d_lids) -> (lid, bs, t, d_lids)
    | uu____2991 -> failwith "Impossible!" in
  match uu____2969 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____3007 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____3007 t in
      let uu____3014 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____3014 with
       | (bs2,t2) ->
           let ibs =
             let uu____3025 =
               let uu____3026 = FStar_Syntax_Subst.compress t2 in
               uu____3026.FStar_Syntax_Syntax.n in
             match uu____3025 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____3033) -> ibs
             | uu____3044 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____3049 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____3050 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____3049 uu____3050 in
           let ind1 =
             let uu____3056 =
               let uu____3057 =
                 FStar_List.map
                   (fun uu____3066  ->
                      match uu____3066 with
                      | (bv,aq) ->
                          let uu____3073 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3073, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____3057 in
             uu____3056 None FStar_Range.dummyRange in
           let ind2 =
             let uu____3081 =
               let uu____3082 =
                 FStar_List.map
                   (fun uu____3091  ->
                      match uu____3091 with
                      | (bv,aq) ->
                          let uu____3098 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____3098, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3082 in
             uu____3081 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____3106 =
               let uu____3107 =
                 let uu____3108 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____3108] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____3107 in
             uu____3106 None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____3123,uu____3124,uu____3125,t_lid,uu____3127,uu____3128)
                      -> t_lid = lid
                  | uu____3131 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___90_3137 = fml in
             let uu____3138 =
               let uu____3139 =
                 let uu____3144 =
                   let uu____3145 =
                     let uu____3152 =
                       let uu____3154 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3154] in
                     [uu____3152] in
                   FStar_Syntax_Syntax.Meta_pattern uu____3145 in
                 (fml, uu____3144) in
               FStar_Syntax_Syntax.Tm_meta uu____3139 in
             {
               FStar_Syntax_Syntax.n = uu____3138;
               FStar_Syntax_Syntax.tk = (uu___90_3137.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___90_3137.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___90_3137.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3169 =
                      let uu____3170 =
                        let uu____3171 =
                          let uu____3172 =
                            let uu____3173 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____3173 None in
                          FStar_Syntax_Syntax.as_arg uu____3172 in
                        [uu____3171] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3170 in
                    uu____3169 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3198 =
                      let uu____3199 =
                        let uu____3200 =
                          let uu____3201 =
                            let uu____3202 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____3202 None in
                          FStar_Syntax_Syntax.as_arg uu____3201 in
                        [uu____3200] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3199 in
                    uu____3198 None FStar_Range.dummyRange) bs2 fml2 in
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
                       (lid,uu____3278,uu____3279,uu____3280,uu____3281,uu____3282)
                       -> lid
                   | uu____3287 -> failwith "Impossible!") tcs in
            let uu____3288 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3296,uu____3297,uu____3298,uu____3299) ->
                  (lid, us)
              | uu____3304 -> failwith "Impossible!" in
            match uu____3288 with
            | (lid,us) ->
                let uu____3310 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3310 with
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
                         let uu____3328 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____3328 fml []
                           FStar_Range.dummyRange in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
let check_inductive_well_typedness:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.sigelt Prims.list*
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____3358 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___82_3373  ->
                    match uu___82_3373 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3374;
                        FStar_Syntax_Syntax.sigrng = uu____3375;
                        FStar_Syntax_Syntax.sigquals = uu____3376;
                        FStar_Syntax_Syntax.sigmeta = uu____3377;_} -> true
                    | uu____3387 -> false)) in
          match uu____3358 with
          | (tys,datas) ->
              ((let uu____3400 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___83_3407  ->
                          match uu___83_3407 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3408;
                              FStar_Syntax_Syntax.sigrng = uu____3409;
                              FStar_Syntax_Syntax.sigquals = uu____3410;
                              FStar_Syntax_Syntax.sigmeta = uu____3411;_} ->
                              false
                          | uu____3420 -> true)) in
                if uu____3400
                then
                  let uu____3421 =
                    let uu____3422 =
                      let uu____3425 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3425) in
                    FStar_Errors.Error uu____3422 in
                  raise uu____3421
                else ());
               (let env0 = env in
                let uu____3428 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3455  ->
                         match uu____3455 with
                         | (env1,all_tcs,g) ->
                             let uu____3477 = tc_tycon env1 tc in
                             (match uu____3477 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3494 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____3494
                                    then
                                      let uu____3495 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3495
                                    else ());
                                   (let uu____3497 =
                                      let uu____3498 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3498 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3497))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3428 with
                | (env1,tcs,g) ->
                    let uu____3523 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3539  ->
                             match uu____3539 with
                             | (datas1,g1) ->
                                 let uu____3550 =
                                   let uu____3553 = tc_data env1 tcs in
                                   uu____3553 se in
                                 (match uu____3550 with
                                  | (data,g') ->
                                      let uu____3563 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____3563))) datas
                        ([], g) in
                    (match uu____3523 with
                     | (datas1,g1) ->
                         let uu____3575 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____3575 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3592 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3592;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (sig_bndle, tcs1, datas2)))))