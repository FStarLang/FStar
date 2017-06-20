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
          let uu____32 = FStar_Syntax_Subst.open_term tps k in
          (match uu____32 with
           | (tps1,k1) ->
               let uu____41 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____41 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____55 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____55 with
                     | (indices,t) ->
                         let uu____79 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____79 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____92 =
                                let uu____95 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____95 with
                                | (t1,uu____102,g) ->
                                    let uu____104 =
                                      let uu____105 =
                                        let uu____106 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____106 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____105 in
                                    (t1, uu____104) in
                              (match uu____92 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____116 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____116 in
                                   let uu____119 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____119 with
                                    | (t_type,u) ->
                                        ((let uu____129 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____129);
                                         (let t_tc =
                                            let uu____133 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____133 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None in
                                          let uu____141 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____141,
                                            (let uu___86_145 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___86_145.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___86_145.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___86_145.FStar_Syntax_Syntax.sigmeta)
                                             }), u, guard)))))))))
      | uu____149 -> failwith "impossible"
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
            let uu____188 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____202  ->
                     match uu____202 with
                     | (se1,u_tc) ->
                         let uu____211 =
                           let uu____212 =
                             let uu____213 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____213 in
                           FStar_Ident.lid_equals tc_lid uu____212 in
                         if uu____211
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____223,uu____224,tps,uu____226,uu____227,uu____228)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____247  ->
                                          match uu____247 with
                                          | (x,uu____254) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____257 =
                                  let uu____261 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____261, tps2, u_tc) in
                                Some uu____257
                            | uu____265 -> failwith "Impossible")
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
            (match uu____188 with
             | (env1,tps,u_tc) ->
                 let uu____304 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____313 =
                     let uu____314 = FStar_Syntax_Subst.compress t1 in
                     uu____314.FStar_Syntax_Syntax.n in
                   match uu____313 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____336 = FStar_Util.first_N ntps bs in
                       (match uu____336 with
                        | (uu____354,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                None t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____386  ->
                                        match uu____386 with
                                        | (x,uu____390) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____391 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____391)
                   | uu____392 -> ([], t1) in
                 (match uu____304 with
                  | (arguments,result) ->
                      ((let uu____413 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                        if uu____413
                        then
                          let uu____414 = FStar_Syntax_Print.lid_to_string c in
                          let uu____415 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments in
                          let uu____416 =
                            FStar_Syntax_Print.term_to_string result in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____414
                            uu____415 uu____416
                        else ());
                       (let uu____418 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments in
                        match uu____418 with
                        | (arguments1,env',us) ->
                            let uu____427 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result in
                            (match uu____427 with
                             | (result1,res_lcomp) ->
                                 ((let uu____435 =
                                     let uu____436 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ in
                                     uu____436.FStar_Syntax_Syntax.n in
                                   match uu____435 with
                                   | FStar_Syntax_Syntax.Tm_type uu____439 ->
                                       ()
                                   | ty ->
                                       let uu____441 =
                                         let uu____442 =
                                           let uu____445 =
                                             let uu____446 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____447 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____446 uu____447 in
                                           (uu____445,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____442 in
                                       raise uu____441);
                                  (let uu____448 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____448 with
                                   | (head1,uu____461) ->
                                       ((let uu____477 =
                                           let uu____478 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____478.FStar_Syntax_Syntax.n in
                                         match uu____477 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____482 ->
                                             let uu____483 =
                                               let uu____484 =
                                                 let uu____487 =
                                                   let uu____488 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____489 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____488 uu____489 in
                                                 (uu____487,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____484 in
                                             raise uu____483);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____494  ->
                                                  fun u_x  ->
                                                    match uu____494 with
                                                    | (x,uu____499) ->
                                                        let uu____500 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____500)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____504 =
                                             let uu____508 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____522  ->
                                                       match uu____522 with
                                                       | (x,uu____529) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____508
                                               arguments1 in
                                           let uu____534 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____504
                                             uu____534 in
                                         ((let uu___87_537 = se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___87_537.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___87_537.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___87_537.FStar_Syntax_Syntax.sigmeta)
                                           }), g))))))))))
        | uu____542 -> failwith "impossible"
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
            let uu___88_582 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_582.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_582.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars, (snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_582.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____588 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____588
           then
             let uu____589 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____589
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____600  ->
                     match uu____600 with
                     | (se,uu____604) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____605,uu____606,tps,k,uu____609,uu____610)
                              ->
                              let uu____615 =
                                let uu____616 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____616 in
                              FStar_Syntax_Syntax.null_binder uu____615
                          | uu____623 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____629,uu____630,t,uu____632,uu____633,uu____634)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____637 -> failwith "Impossible")) in
           let t =
             let uu____641 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____641 in
           (let uu____645 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____645
            then
              let uu____646 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____646
            else ());
           (let uu____648 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____648 with
            | (uvs,t1) ->
                ((let uu____658 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____658
                  then
                    let uu____659 =
                      let uu____660 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____660
                        (FStar_String.concat ", ") in
                    let uu____666 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____659 uu____666
                  else ());
                 (let uu____668 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____668 with
                  | (uvs1,t2) ->
                      let uu____677 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____677 with
                       | (args,uu____690) ->
                           let uu____701 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____701 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____740  ->
                                       fun uu____741  ->
                                         match (uu____740, uu____741) with
                                         | ((x,uu____751),(se,uu____753)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____759,tps,uu____761,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____769 =
                                                    let uu____777 =
                                                      let uu____778 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____778.FStar_Syntax_Syntax.n in
                                                    match uu____777 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____800 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____800 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____845 ->
                                                                   let uu____849
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____849
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____868 -> ([], ty) in
                                                  (match uu____769 with
                                                   | (tps1,t3) ->
                                                       let uu___89_886 = se in
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
                                                           (uu___89_886.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___89_886.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___89_886.FStar_Syntax_Syntax.sigmeta)
                                                       })
                                              | uu____894 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____898 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_39  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_39)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_915  ->
                                                match uu___82_915 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____920,uu____921,uu____922,uu____923,uu____924);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____925;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____926;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____927;_}
                                                    -> (tc, uvs_universes)
                                                | uu____934 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____940  ->
                                           fun d  ->
                                             match uu____940 with
                                             | (t3,uu____945) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____947,uu____948,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____955 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____955
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___90_956 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_956.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___90_956.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___90_956.FStar_Syntax_Syntax.sigmeta)
                                                      }
                                                  | uu____958 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____969 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____969
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____979 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____979
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv* FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____989 =
      let uu____990 = FStar_Syntax_Subst.compress t in
      uu____990.FStar_Syntax_Syntax.n in
    match uu____989 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1006 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1009 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1032 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1044  ->
               match uu____1044 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1064 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        fst uu____1064 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env (
                                    fst a) (fst a'))) true args l))
            uu____1032
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1161 =
             let uu____1162 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1162 in
           debug_log env uu____1161);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1165 =
              let uu____1166 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1166 in
            debug_log env uu____1165);
           (let uu____1167 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1167) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1169 =
                  let uu____1170 = FStar_Syntax_Subst.compress btype1 in
                  uu____1170.FStar_Syntax_Syntax.n in
                match uu____1169 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1189 = try_get_fv t in
                    (match uu____1189 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1201  ->
                                 match uu____1201 with
                                 | (t1,uu____1205) ->
                                     let uu____1206 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1206) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1226 =
                        let uu____1227 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1227 in
                      if uu____1226
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1233  ->
                               match uu____1233 with
                               | (b,uu____1237) ->
                                   let uu____1238 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1238) sbs)
                           &&
                           ((let uu____1239 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1239 with
                             | (uu____1242,return_type) ->
                                 let uu____1244 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1244)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1245 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1247 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1250) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1257) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1263,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1298  ->
                          match uu____1298 with
                          | (p,uu____1306,t) ->
                              let bs =
                                let uu____1316 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1316 in
                              let uu____1318 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1318 with
                               | (bs1,t1) ->
                                   let uu____1323 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1323)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1325,uu____1326)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1356 ->
                    ((let uu____1358 =
                        let uu____1359 =
                          let uu____1360 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____1361 =
                            let uu____1362 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____1362 in
                          Prims.strcat uu____1360 uu____1361 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1359 in
                      debug_log env uu____1358);
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
              (let uu____1370 =
                 let uu____1371 =
                   let uu____1372 =
                     let uu____1373 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1373 in
                   Prims.strcat ilid.FStar_Ident.str uu____1372 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1371 in
               debug_log env uu____1370);
              (let uu____1374 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1374 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1384 =
                        already_unfolded ilid args unfolded env in
                      if uu____1384
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1389 =
                            let uu____1390 =
                              let uu____1391 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1391
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1390 in
                          debug_log env uu____1389);
                         (let uu____1393 =
                            let uu____1394 = FStar_ST.read unfolded in
                            let uu____1398 =
                              let uu____1402 =
                                let uu____1410 =
                                  let uu____1416 =
                                    FStar_List.splitAt num_ibs args in
                                  fst uu____1416 in
                                (ilid, uu____1410) in
                              [uu____1402] in
                            FStar_List.append uu____1394 uu____1398 in
                          FStar_ST.write unfolded uu____1393);
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
                  (let uu____1474 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1474 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____1485 ->
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
                         (let uu____1488 =
                            let uu____1489 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1489 in
                          debug_log env uu____1488);
                         (let uu____1490 =
                            let uu____1491 = FStar_Syntax_Subst.compress dt1 in
                            uu____1491.FStar_Syntax_Syntax.n in
                          match uu____1490 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1507 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1507 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____1534 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1534 dbs1 in
                                    let c1 =
                                      let uu____1537 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1537 c in
                                    let uu____1539 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1539 with
                                     | (args1,uu____1557) ->
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
                                           let uu____1603 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1603 c1 in
                                         ((let uu____1614 =
                                             let uu____1615 =
                                               let uu____1616 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____1617 =
                                                 let uu____1618 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____1618 in
                                               Prims.strcat uu____1616
                                                 uu____1617 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1615 in
                                           debug_log env uu____1614);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1619 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1621 =
                                  let uu____1622 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____1622.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1621
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
                   (let uu____1648 = try_get_fv t1 in
                    match uu____1648 with
                    | (fv,uu____1652) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1671 =
                      let uu____1672 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1672 in
                    debug_log env uu____1671);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____1674 =
                      FStar_List.fold_left
                        (fun uu____1681  ->
                           fun b  ->
                             match uu____1681 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1694 =
                                      ty_strictly_positive_in_type ty_lid
                                        (fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____1695 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____1694, uu____1695))) (true, env)
                        sbs1 in
                    match uu____1674 with | (b,uu____1701) -> b))
              | uu____1702 ->
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
              let uu____1727 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____1727 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____1738 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1740 =
                      let uu____1741 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1741 in
                    debug_log env uu____1740);
                   (let uu____1742 =
                      let uu____1743 = FStar_Syntax_Subst.compress dt in
                      uu____1743.FStar_Syntax_Syntax.n in
                    match uu____1742 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1746 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1749) ->
                        let dbs1 =
                          let uu____1764 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          snd uu____1764 in
                        let dbs2 =
                          let uu____1788 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1788 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____1792 =
                            let uu____1793 =
                              let uu____1794 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____1794 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1793 in
                          debug_log env uu____1792);
                         (let uu____1803 =
                            FStar_List.fold_left
                              (fun uu____1810  ->
                                 fun b  ->
                                   match uu____1810 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1823 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____1824 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____1823, uu____1824)))
                              (true, env) dbs3 in
                          match uu____1803 with | (b,uu____1830) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1831,uu____1832) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1848 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____1868 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1878,uu____1879,uu____1880) -> (lid, us, bs)
        | uu____1885 -> failwith "Impossible!" in
      match uu____1868 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1892 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____1892 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____1907 =
                 let uu____1909 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 snd uu____1909 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1915 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1915
                      unfolded_inductives env2) uu____1907)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1923,uu____1924,t,uu____1926,uu____1927,uu____1928) -> t
    | uu____1931 -> failwith "Impossible!"
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
          let uu____1952 =
            let uu____1953 = FStar_Syntax_Subst.compress dt1 in
            uu____1953.FStar_Syntax_Syntax.n in
          match uu____1952 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1957) ->
              let dbs1 =
                let uu____1972 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                snd uu____1972 in
              let dbs2 =
                let uu____1996 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____1996 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____2005 =
                           let uu____2006 =
                             let uu____2007 =
                               FStar_Syntax_Syntax.as_arg
                                 (fst b).FStar_Syntax_Syntax.sort in
                             [uu____2007] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____2006 in
                         uu____2005 None FStar_Range.dummyRange in
                       let sort_range =
                         ((fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____2014 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____2014 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2019 =
                       let uu____2020 =
                         let uu____2021 =
                           let uu____2022 =
                             let uu____2023 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs [((fst b), None)]
                               uu____2023 None in
                           FStar_Syntax_Syntax.as_arg uu____2022 in
                         [uu____2021] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2020 in
                     uu____2019 None FStar_Range.dummyRange) dbs3 cond
          | uu____2035 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2101 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2113,bs,t,uu____2116,d_lids) -> (lid, bs, t, d_lids)
    | uu____2123 -> failwith "Impossible!" in
  match uu____2101 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2148 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2148 t in
      let uu____2158 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2158 with
       | (bs2,t2) ->
           let ibs =
             let uu____2178 =
               let uu____2179 = FStar_Syntax_Subst.compress t2 in
               uu____2179.FStar_Syntax_Syntax.n in
             match uu____2178 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2186) -> ibs
             | uu____2197 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2202 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2203 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2202 uu____2203 in
           let ind1 =
             let uu____2208 =
               let uu____2209 =
                 FStar_List.map
                   (fun uu____2214  ->
                      match uu____2214 with
                      | (bv,aq) ->
                          let uu____2221 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2221, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2209 in
             uu____2208 None FStar_Range.dummyRange in
           let ind2 =
             let uu____2229 =
               let uu____2230 =
                 FStar_List.map
                   (fun uu____2235  ->
                      match uu____2235 with
                      | (bv,aq) ->
                          let uu____2242 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2242, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2230 in
             uu____2229 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2250 =
               let uu____2251 =
                 let uu____2252 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2252] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2251 in
             uu____2250 None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2266 = acc in
                  match uu____2266 with
                  | (uu____2274,en,uu____2276,uu____2277) ->
                      let opt =
                        let uu____2286 =
                          let uu____2287 = FStar_Syntax_Util.type_u () in
                          fst uu____2287 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (fst b).FStar_Syntax_Syntax.sort uu____2286 false in
                      (match opt with
                       | None  -> false
                       | Some uu____2290 -> true)) bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2294 =
                      let uu____2295 =
                        let uu____2296 =
                          let uu____2297 =
                            let uu____2298 =
                              FStar_Syntax_Syntax.bv_to_name (fst b) in
                            FStar_Syntax_Syntax.as_arg uu____2298 in
                          [uu____2297] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2296 in
                      uu____2295 None FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____2294)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___91_2307 = fml in
             let uu____2308 =
               let uu____2309 =
                 let uu____2314 =
                   let uu____2315 =
                     let uu____2322 =
                       let uu____2324 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2324] in
                     [uu____2322] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2315 in
                 (fml, uu____2314) in
               FStar_Syntax_Syntax.Tm_meta uu____2309 in
             {
               FStar_Syntax_Syntax.n = uu____2308;
               FStar_Syntax_Syntax.tk = (uu___91_2307.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___91_2307.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___91_2307.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2336 =
                      let uu____2337 =
                        let uu____2338 =
                          let uu____2339 =
                            let uu____2340 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2340 None in
                          FStar_Syntax_Syntax.as_arg uu____2339 in
                        [uu____2338] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2337 in
                    uu____2336 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2357 =
                      let uu____2358 =
                        let uu____2359 =
                          let uu____2360 =
                            let uu____2361 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2361 None in
                          FStar_Syntax_Syntax.as_arg uu____2360 in
                        [uu____2359] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2358 in
                    uu____2357 None FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____2376 = acc in
           (match uu____2376 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2410,uu____2411,uu____2412,t_lid,uu____2414,uu____2415)
                           -> t_lid = lid
                       | uu____2418 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2422 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____2422)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____2424 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____2427 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2424, uu____2427)))
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
                  (uu____2498,us,uu____2500,uu____2501,uu____2502,uu____2503)
                  -> us
              | uu____2508 -> failwith "Impossible!" in
            let uu____2509 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2509 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____2525 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2525 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2557 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____2557 with
                       | (phi1,uu____2562) ->
                           ((let uu____2564 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____2564
                             then
                               let uu____2565 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2565
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2573  ->
                                      match uu____2573 with
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
                let uu____2622 =
                  let uu____2623 = FStar_Syntax_Subst.compress t in
                  uu____2623.FStar_Syntax_Syntax.n in
                match uu____2622 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2633) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2660 = is_mutual t' in
                    if uu____2660
                    then true
                    else
                      (let uu____2662 =
                         FStar_List.map FStar_Pervasives.fst args in
                       exists_mutual uu____2662)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2675) -> is_mutual t'
                | uu____2680 -> false
              and exists_mutual uu___83_2681 =
                match uu___83_2681 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____2698 =
                let uu____2699 = FStar_Syntax_Subst.compress dt1 in
                uu____2699.FStar_Syntax_Syntax.n in
              match uu____2698 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2705) ->
                  let dbs1 =
                    let uu____2720 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    snd uu____2720 in
                  let dbs2 =
                    let uu____2744 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2744 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2756 =
                               let uu____2757 =
                                 let uu____2758 =
                                   FStar_Syntax_Syntax.as_arg
                                     (fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2758] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2757 in
                             uu____2756 None FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____2764 = is_mutual sort in
                             if uu____2764
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2771 =
                             let uu____2772 =
                               let uu____2773 =
                                 let uu____2774 =
                                   let uu____2775 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs [((fst b), None)]
                                     uu____2775 None in
                                 FStar_Syntax_Syntax.as_arg uu____2774 in
                               [uu____2773] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2772 in
                           uu____2771 None FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2787 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2837 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2849,bs,t,uu____2852,d_lids) -> (lid, bs, t, d_lids)
    | uu____2859 -> failwith "Impossible!" in
  match uu____2837 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2875 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2875 t in
      let uu____2885 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2885 with
       | (bs2,t2) ->
           let ibs =
             let uu____2896 =
               let uu____2897 = FStar_Syntax_Subst.compress t2 in
               uu____2897.FStar_Syntax_Syntax.n in
             match uu____2896 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2904) -> ibs
             | uu____2915 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2920 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2921 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2920 uu____2921 in
           let ind1 =
             let uu____2926 =
               let uu____2927 =
                 FStar_List.map
                   (fun uu____2932  ->
                      match uu____2932 with
                      | (bv,aq) ->
                          let uu____2939 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2939, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2927 in
             uu____2926 None FStar_Range.dummyRange in
           let ind2 =
             let uu____2947 =
               let uu____2948 =
                 FStar_List.map
                   (fun uu____2953  ->
                      match uu____2953 with
                      | (bv,aq) ->
                          let uu____2960 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2960, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2948 in
             uu____2947 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2968 =
               let uu____2969 =
                 let uu____2970 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2970] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2969 in
             uu____2968 None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2978,uu____2979,uu____2980,t_lid,uu____2982,uu____2983)
                      -> t_lid = lid
                  | uu____2986 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___92_2992 = fml in
             let uu____2993 =
               let uu____2994 =
                 let uu____2999 =
                   let uu____3000 =
                     let uu____3007 =
                       let uu____3009 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____3009] in
                     [uu____3007] in
                   FStar_Syntax_Syntax.Meta_pattern uu____3000 in
                 (fml, uu____2999) in
               FStar_Syntax_Syntax.Tm_meta uu____2994 in
             {
               FStar_Syntax_Syntax.n = uu____2993;
               FStar_Syntax_Syntax.tk = (uu___92_2992.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___92_2992.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___92_2992.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3021 =
                      let uu____3022 =
                        let uu____3023 =
                          let uu____3024 =
                            let uu____3025 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____3025 None in
                          FStar_Syntax_Syntax.as_arg uu____3024 in
                        [uu____3023] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3022 in
                    uu____3021 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3042 =
                      let uu____3043 =
                        let uu____3044 =
                          let uu____3045 =
                            let uu____3046 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____3046 None in
                          FStar_Syntax_Syntax.as_arg uu____3045 in
                        [uu____3044] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3043 in
                    uu____3042 None FStar_Range.dummyRange) bs2 fml2 in
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
                       (lid,uu____3115,uu____3116,uu____3117,uu____3118,uu____3119)
                       -> lid
                   | uu____3124 -> failwith "Impossible!") tcs in
            let uu____3125 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3133,uu____3134,uu____3135,uu____3136) ->
                  (lid, us)
              | uu____3141 -> failwith "Impossible!" in
            match uu____3125 with
            | (lid,us) ->
                let uu____3147 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3147 with
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
                         let uu____3165 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____3165 fml []
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
          let uu____3199 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_3209  ->
                    match uu___84_3209 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3210;
                        FStar_Syntax_Syntax.sigrng = uu____3211;
                        FStar_Syntax_Syntax.sigquals = uu____3212;
                        FStar_Syntax_Syntax.sigmeta = uu____3213;_} -> true
                    | uu____3223 -> false)) in
          match uu____3199 with
          | (tys,datas) ->
              ((let uu____3236 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_3238  ->
                          match uu___85_3238 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3239;
                              FStar_Syntax_Syntax.sigrng = uu____3240;
                              FStar_Syntax_Syntax.sigquals = uu____3241;
                              FStar_Syntax_Syntax.sigmeta = uu____3242;_} ->
                              false
                          | uu____3251 -> true)) in
                if uu____3236
                then
                  let uu____3252 =
                    let uu____3253 =
                      let uu____3256 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3256) in
                    FStar_Errors.Error uu____3253 in
                  raise uu____3252
                else ());
               (let env0 = env in
                let uu____3259 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3273  ->
                         match uu____3273 with
                         | (env1,all_tcs,g) ->
                             let uu____3295 = tc_tycon env1 tc in
                             (match uu____3295 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3312 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____3312
                                    then
                                      let uu____3313 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3313
                                    else ());
                                   (let uu____3315 =
                                      let uu____3316 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3316 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3315))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3259 with
                | (env1,tcs,g) ->
                    let uu____3341 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3349  ->
                             match uu____3349 with
                             | (datas1,g1) ->
                                 let uu____3360 =
                                   let uu____3363 = tc_data env1 tcs in
                                   uu____3363 se in
                                 (match uu____3360 with
                                  | (data,g') ->
                                      let uu____3373 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____3373))) datas
                        ([], g) in
                    (match uu____3341 with
                     | (datas1,g1) ->
                         let uu____3385 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____3385 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3402 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3402;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (sig_bndle, tcs1, datas2)))))