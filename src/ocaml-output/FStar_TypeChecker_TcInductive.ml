open Prims
let tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let uu____30 = FStar_Syntax_Subst.open_term tps k  in
          (match uu____30 with
           | (tps1,k1) ->
               let uu____39 = FStar_TypeChecker_TcTerm.tc_binders env tps1
                  in
               (match uu____39 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1
                       in
                    let uu____53 = FStar_Syntax_Util.arrow_formals k2  in
                    (match uu____53 with
                     | (indices,t) ->
                         let uu____77 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____77 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____90 =
                                let uu____93 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____93 with
                                | (t1,uu____100,g) ->
                                    let uu____102 =
                                      let uu____103 =
                                        let uu____104 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____104
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____103
                                       in
                                    (t1, uu____102)
                                 in
                              (match uu____90 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____114 =
                                       FStar_Syntax_Syntax.mk_Total t1  in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____114
                                      in
                                   let uu____117 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____117 with
                                    | (t_type,u) ->
                                        ((let uu____127 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____127);
                                         (let t_tc =
                                            let uu____131 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____131
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
                                              None
                                             in
                                          let uu____139 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (uu____139,
                                            (let uu___86_143 = s  in
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
                                                 (uu___86_143.FStar_Syntax_Syntax.sigmeta)
                                             }), u, guard)))))))))
      | uu____147 -> failwith "impossible"
  
let tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____184 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____198  ->
                     match uu____198 with
                     | (se1,u_tc) ->
                         let uu____207 =
                           let uu____208 =
                             let uu____209 =
                               FStar_Syntax_Util.lid_of_sigelt se1  in
                             FStar_Util.must uu____209  in
                           FStar_Ident.lid_equals tc_lid uu____208  in
                         if uu____207
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____219,uu____220,tps,uu____222,uu____223,uu____224)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____243  ->
                                          match uu____243 with
                                          | (x,uu____250) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____253 =
                                  let uu____257 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____257, tps2, u_tc)  in
                                Some uu____253
                            | uu____261 -> failwith "Impossible")
                         else None)
                 in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng)))
               in
            (match uu____184 with
             | (env1,tps,u_tc) ->
                 let uu____300 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t
                      in
                   let uu____309 =
                     let uu____310 = FStar_Syntax_Subst.compress t1  in
                     uu____310.FStar_Syntax_Syntax.n  in
                   match uu____309 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____332 = FStar_Util.first_N ntps bs  in
                       (match uu____332 with
                        | (uu____350,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                None t1.FStar_Syntax_Syntax.pos
                               in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____382  ->
                                        match uu____382 with
                                        | (x,uu____386) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____387 =
                              FStar_Syntax_Subst.subst subst1 t2  in
                            FStar_Syntax_Util.arrow_formals uu____387)
                   | uu____388 -> ([], t1)  in
                 (match uu____300 with
                  | (arguments,result) ->
                      ((let uu____409 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____409
                        then
                          let uu____410 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____411 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____412 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____410
                            uu____411 uu____412
                        else ());
                       (let uu____414 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____414 with
                        | (arguments1,env',us) ->
                            let uu____423 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____423 with
                             | (result1,res_lcomp) ->
                                 ((let uu____431 =
                                     let uu____432 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                        in
                                     uu____432.FStar_Syntax_Syntax.n  in
                                   match uu____431 with
                                   | FStar_Syntax_Syntax.Tm_type uu____435 ->
                                       ()
                                   | ty ->
                                       let uu____437 =
                                         let uu____438 =
                                           let uu____441 =
                                             let uu____442 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1
                                                in
                                             let uu____443 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____442 uu____443
                                              in
                                           (uu____441,
                                             (se.FStar_Syntax_Syntax.sigrng))
                                            in
                                         FStar_Errors.Error uu____438  in
                                       raise uu____437);
                                  (let uu____444 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____444 with
                                   | (head1,uu____457) ->
                                       ((let uu____473 =
                                           let uu____474 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____474.FStar_Syntax_Syntax.n
                                            in
                                         match uu____473 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____478 ->
                                             let uu____479 =
                                               let uu____480 =
                                                 let uu____483 =
                                                   let uu____484 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid
                                                      in
                                                   let uu____485 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1
                                                      in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____484 uu____485
                                                    in
                                                 (uu____483,
                                                   (se.FStar_Syntax_Syntax.sigrng))
                                                  in
                                               FStar_Errors.Error uu____480
                                                in
                                             raise uu____479);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____490  ->
                                                  fun u_x  ->
                                                    match uu____490 with
                                                    | (x,uu____495) ->
                                                        let uu____496 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____496)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____500 =
                                             let uu____504 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____518  ->
                                                       match uu____518 with
                                                       | (x,uu____525) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____504
                                               arguments1
                                              in
                                           let uu____530 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1
                                              in
                                           FStar_Syntax_Util.arrow uu____500
                                             uu____530
                                            in
                                         ((let uu___87_533 = se  in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___87_533.FStar_Syntax_Syntax.sigrng);
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___87_533.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___87_533.FStar_Syntax_Syntax.sigmeta)
                                           }), g))))))))))
        | uu____538 -> failwith "impossible"
  
let generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list
        ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars = FStar_List.map FStar_Pervasives.snd tcs  in
          let g1 =
            let uu___88_574 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_574.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_574.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars, (snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_574.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____580 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____580
           then
             let uu____581 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____581
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____592  ->
                     match uu____592 with
                     | (se,uu____596) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____597,uu____598,tps,k,uu____601,uu____602)
                              ->
                              let uu____607 =
                                let uu____608 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____608
                                 in
                              FStar_Syntax_Syntax.null_binder uu____607
                          | uu____615 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____621,uu____622,t,uu____624,uu____625,uu____626)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____629 -> failwith "Impossible"))
              in
           let t =
             let uu____633 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit
                in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____633
              in
           (let uu____637 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____637
            then
              let uu____638 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____638
            else ());
           (let uu____640 = FStar_TypeChecker_Util.generalize_universes env t
               in
            match uu____640 with
            | (uvs,t1) ->
                ((let uu____650 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____650
                  then
                    let uu____651 =
                      let uu____652 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____652
                        (FStar_String.concat ", ")
                       in
                    let uu____658 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____651 uu____658
                  else ());
                 (let uu____660 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____660 with
                  | (uvs1,t2) ->
                      let uu____669 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____669 with
                       | (args,uu____682) ->
                           let uu____693 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____693 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____730  ->
                                       fun uu____731  ->
                                         match (uu____730, uu____731) with
                                         | ((x,uu____741),(se,uu____743)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____749,tps,uu____751,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____759 =
                                                    let uu____767 =
                                                      let uu____768 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____768.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____767 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____790 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____790 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____833 ->
                                                                   let uu____837
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk
                                                                     in
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    uu____837
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____856 -> ([], ty)
                                                     in
                                                  (match uu____759 with
                                                   | (tps1,t3) ->
                                                       let uu___89_874 = se
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
                                                           (uu___89_874.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___89_874.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___89_874.FStar_Syntax_Syntax.sigmeta)
                                                       })
                                              | uu____882 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____886 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_39  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_39))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_903  ->
                                                match uu___82_903 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____908,uu____909,uu____910,uu____911,uu____912);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____913;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____914;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____915;_}
                                                    -> (tc, uvs_universes)
                                                | uu____922 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____928  ->
                                           fun d  ->
                                             match uu____928 with
                                             | (t3,uu____933) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____935,uu____936,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____943 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____943
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___90_944 = d  in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_944.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___90_944.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___90_944.FStar_Syntax_Syntax.sigmeta)
                                                      }
                                                  | uu____946 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____955 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____955
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____963 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____963
  
let try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____972 =
      let uu____973 = FStar_Syntax_Subst.compress t  in
      uu____973.FStar_Syntax_Syntax.n  in
    match uu____972 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____989 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____992 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____1011 = FStar_ST.read unfolded  in
          FStar_List.existsML
            (fun uu____1023  ->
               match uu____1023 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1043 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        fst uu____1043  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env (
                                    fst a) (fst a'))) true args l))
            uu____1011
  
let rec ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1138 =
             let uu____1139 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____1139
              in
           debug_log env uu____1138);
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
           (let uu____1142 =
              let uu____1143 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1143
               in
            debug_log env uu____1142);
           (let uu____1144 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____1144) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1146 =
                  let uu____1147 = FStar_Syntax_Subst.compress btype1  in
                  uu____1147.FStar_Syntax_Syntax.n  in
                match uu____1146 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1166 = try_get_fv t  in
                    (match uu____1166 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1178  ->
                                 match uu____1178 with
                                 | (t1,uu____1182) ->
                                     let uu____1183 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____1183) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1203 =
                        let uu____1204 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____1204  in
                      if uu____1203
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1210  ->
                               match uu____1210 with
                               | (b,uu____1214) ->
                                   let uu____1215 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____1215) sbs)
                           &&
                           ((let uu____1216 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____1216 with
                             | (uu____1219,return_type) ->
                                 let uu____1221 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1221)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1222 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1224 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1227) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1234) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1240,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1275  ->
                          match uu____1275 with
                          | (p,uu____1283,t) ->
                              let bs =
                                let uu____1293 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1293
                                 in
                              let uu____1295 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____1295 with
                               | (bs1,t1) ->
                                   let uu____1300 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1300)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1302,uu____1303)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1333 ->
                    ((let uu____1335 =
                        let uu____1336 =
                          let uu____1337 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____1338 =
                            let uu____1339 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____1339  in
                          Prims.strcat uu____1337 uu____1338  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1336
                         in
                      debug_log env uu____1335);
                     false)))))

and ty_nested_positive_in_inductive :
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
              (let uu____1347 =
                 let uu____1348 =
                   let uu____1349 =
                     let uu____1350 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____1350  in
                   Prims.strcat ilid.FStar_Ident.str uu____1349  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1348
                  in
               debug_log env uu____1347);
              (let uu____1351 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____1351 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1361 =
                        already_unfolded ilid args unfolded env  in
                      if uu____1361
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____1366 =
                            let uu____1367 =
                              let uu____1368 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____1368
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1367
                             in
                          debug_log env uu____1366);
                         (let uu____1370 =
                            let uu____1371 = FStar_ST.read unfolded  in
                            let uu____1375 =
                              let uu____1379 =
                                let uu____1387 =
                                  let uu____1393 =
                                    FStar_List.splitAt num_ibs args  in
                                  fst uu____1393  in
                                (ilid, uu____1387)  in
                              [uu____1379]  in
                            FStar_List.append uu____1371 uu____1375  in
                          FStar_ST.write unfolded uu____1370);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))

and ty_nested_positive_in_dlid :
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
                  (let uu____1451 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____1451 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____1462 ->
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
                         (let uu____1465 =
                            let uu____1466 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1466
                             in
                          debug_log env uu____1465);
                         (let uu____1467 =
                            let uu____1468 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____1468.FStar_Syntax_Syntax.n  in
                          match uu____1467 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1484 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____1484 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____1511 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1511 dbs1
                                       in
                                    let c1 =
                                      let uu____1514 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1514 c
                                       in
                                    let uu____1516 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____1516 with
                                     | (args1,uu____1534) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((fst ib),
                                                           (fst arg))]) []
                                             ibs1 args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____1580 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1580 c1
                                            in
                                         ((let uu____1588 =
                                             let uu____1589 =
                                               let uu____1590 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____1591 =
                                                 let uu____1592 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____1592
                                                  in
                                               Prims.strcat uu____1590
                                                 uu____1591
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1589
                                              in
                                           debug_log env uu____1588);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1593 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1595 =
                                  let uu____1596 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____1596.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____1595
                                  ilid num_ibs unfolded env))))))

and ty_nested_positive_in_type :
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
                   (let uu____1622 = try_get_fv t1  in
                    match uu____1622 with
                    | (fv,uu____1626) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1645 =
                      let uu____1646 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1646
                       in
                    debug_log env uu____1645);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____1648 =
                      FStar_List.fold_left
                        (fun uu____1655  ->
                           fun b  ->
                             match uu____1655 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1668 =
                                      ty_strictly_positive_in_type ty_lid
                                        (fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____1669 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____1668, uu____1669))) (true, env)
                        sbs1
                       in
                    match uu____1648 with | (b,uu____1675) -> b))
              | uu____1676 ->
                  failwith "Nested positive check, unhandled case"

let ty_positive_in_datacon :
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
              let uu____1695 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____1695 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____1706 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1708 =
                      let uu____1709 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____1709
                       in
                    debug_log env uu____1708);
                   (let uu____1710 =
                      let uu____1711 = FStar_Syntax_Subst.compress dt  in
                      uu____1711.FStar_Syntax_Syntax.n  in
                    match uu____1710 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1714 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1717) ->
                        let dbs1 =
                          let uu____1732 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          snd uu____1732  in
                        let dbs2 =
                          let uu____1754 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____1754 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____1758 =
                            let uu____1759 =
                              let uu____1760 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____1760 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1759
                             in
                          debug_log env uu____1758);
                         (let uu____1766 =
                            FStar_List.fold_left
                              (fun uu____1773  ->
                                 fun b  ->
                                   match uu____1773 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1786 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____1787 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____1786, uu____1787)))
                              (true, env) dbs3
                             in
                          match uu____1766 with | (b,uu____1793) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1794,uu____1795) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1811 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____1829 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1839,uu____1840,uu____1841) -> (lid, us, bs)
        | uu____1846 -> failwith "Impossible!"  in
      match uu____1829 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1853 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____1853 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____1868 =
                 let uu____1870 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 snd uu____1870  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1876 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1876
                      unfolded_inductives env2) uu____1868)
  
let datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1883,uu____1884,t,uu____1886,uu____1887,uu____1888) -> t
    | uu____1891 -> failwith "Impossible!"
  
let optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____1908 =
            let uu____1909 = FStar_Syntax_Subst.compress dt1  in
            uu____1909.FStar_Syntax_Syntax.n  in
          match uu____1908 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1913) ->
              let dbs1 =
                let uu____1928 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                snd uu____1928  in
              let dbs2 =
                let uu____1950 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____1950 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1959 =
                           let uu____1960 =
                             let uu____1961 =
                               FStar_Syntax_Syntax.as_arg
                                 (fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____1961]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1960
                            in
                         uu____1959 None FStar_Range.dummyRange  in
                       let sort_range =
                         ((fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____1968 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____1968 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____1973 =
                       let uu____1974 =
                         let uu____1975 =
                           let uu____1976 =
                             let uu____1977 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs [((fst b), None)]
                               uu____1977 None
                              in
                           FStar_Syntax_Syntax.as_arg uu____1976  in
                         [uu____1975]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____1974
                        in
                     uu____1973 None FStar_Range.dummyRange) dbs3 cond
          | uu____1989 -> FStar_Syntax_Util.t_true
  
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2048 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2060,bs,t,uu____2063,d_lids) -> (lid, bs, t, d_lids)
    | uu____2070 -> failwith "Impossible!"  in
  match uu____2048 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2095 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2095 t  in
      let uu____2102 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2102 with
       | (bs2,t2) ->
           let ibs =
             let uu____2122 =
               let uu____2123 = FStar_Syntax_Subst.compress t2  in
               uu____2123.FStar_Syntax_Syntax.n  in
             match uu____2122 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2130) -> ibs
             | uu____2141 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2146 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2147 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2146 uu____2147  in
           let ind1 =
             let uu____2152 =
               let uu____2153 =
                 FStar_List.map
                   (fun uu____2158  ->
                      match uu____2158 with
                      | (bv,aq) ->
                          let uu____2165 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2165, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2153  in
             uu____2152 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2173 =
               let uu____2174 =
                 FStar_List.map
                   (fun uu____2179  ->
                      match uu____2179 with
                      | (bv,aq) ->
                          let uu____2186 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2186, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2174  in
             uu____2173 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2194 =
               let uu____2195 =
                 let uu____2196 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2196]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2195
                in
             uu____2194 None FStar_Range.dummyRange  in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2210 = acc  in
                  match uu____2210 with
                  | (uu____2218,en,uu____2220,uu____2221) ->
                      let opt =
                        let uu____2230 =
                          let uu____2231 = FStar_Syntax_Util.type_u ()  in
                          fst uu____2231  in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (fst b).FStar_Syntax_Syntax.sort uu____2230 false
                         in
                      (match opt with
                       | None  -> false
                       | Some uu____2234 -> true)) bs2
              in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2238 =
                      let uu____2239 =
                        let uu____2240 =
                          let uu____2241 =
                            let uu____2242 =
                              FStar_Syntax_Syntax.bv_to_name (fst b)  in
                            FStar_Syntax_Syntax.as_arg uu____2242  in
                          [uu____2241]  in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2240
                         in
                      uu____2239 None FStar_Range.dummyRange  in
                    FStar_Syntax_Util.mk_conj t3 uu____2238)
               FStar_Syntax_Util.t_true bs'
              in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
           let fml1 =
             let uu___91_2251 = fml  in
             let uu____2252 =
               let uu____2253 =
                 let uu____2258 =
                   let uu____2259 =
                     let uu____2266 =
                       let uu____2268 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2268]  in
                     [uu____2266]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2259  in
                 (fml, uu____2258)  in
               FStar_Syntax_Syntax.Tm_meta uu____2253  in
             {
               FStar_Syntax_Syntax.n = uu____2252;
               FStar_Syntax_Syntax.tk = (uu___91_2251.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___91_2251.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___91_2251.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2280 =
                      let uu____2281 =
                        let uu____2282 =
                          let uu____2283 =
                            let uu____2284 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2284 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2283  in
                        [uu____2282]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2281
                       in
                    uu____2280 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2301 =
                      let uu____2302 =
                        let uu____2303 =
                          let uu____2304 =
                            let uu____2305 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2305 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2304  in
                        [uu____2303]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2302
                       in
                    uu____2301 None FStar_Range.dummyRange) bs2 fml2
              in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3  in
           let uu____2320 = acc  in
           (match uu____2320 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2  in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1  in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2354,uu____2355,uu____2356,t_lid,uu____2358,uu____2359)
                           -> t_lid = lid
                       | uu____2362 -> failwith "Impossible")
                    all_datas_in_the_bundle
                   in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2366 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2
                            in
                         FStar_Syntax_Util.mk_conj acc1 uu____2366)
                    FStar_Syntax_Util.t_true t_datas
                   in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")])
                   in
                let uu____2368 = FStar_Syntax_Util.mk_conj guard' guard  in
                let uu____2371 = FStar_Syntax_Util.mk_conj cond' cond  in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2368, uu____2371)))
  
let optimized_haseq_scheme :
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
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (uu____2437,us,uu____2439,uu____2440,uu____2441,uu____2442)
                  -> us
              | uu____2447 -> failwith "Impossible!"  in
            let uu____2448 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____2448 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____2464 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____2464 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____2496 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____2496 with
                       | (phi1,uu____2501) ->
                           ((let uu____2503 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____2503
                             then
                               let uu____2504 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2504
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2512  ->
                                      match uu____2512 with
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
  
let unoptimized_haseq_data :
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
                let uu____2555 =
                  let uu____2556 = FStar_Syntax_Subst.compress t  in
                  uu____2556.FStar_Syntax_Syntax.n  in
                match uu____2555 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2566) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2593 = is_mutual t'  in
                    if uu____2593
                    then true
                    else
                      (let uu____2595 =
                         FStar_List.map FStar_Pervasives.fst args  in
                       exists_mutual uu____2595)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2608) -> is_mutual t'
                | uu____2613 -> false
              
              and exists_mutual uu___83_2614 =
                match uu___83_2614 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____2631 =
                let uu____2632 = FStar_Syntax_Subst.compress dt1  in
                uu____2632.FStar_Syntax_Syntax.n  in
              match uu____2631 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2638) ->
                  let dbs1 =
                    let uu____2653 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    snd uu____2653  in
                  let dbs2 =
                    let uu____2675 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____2675 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (fst b).FStar_Syntax_Syntax.sort  in
                           let haseq_sort =
                             let uu____2687 =
                               let uu____2688 =
                                 let uu____2689 =
                                   FStar_Syntax_Syntax.as_arg
                                     (fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____2689]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2688
                                in
                             uu____2687 None FStar_Range.dummyRange  in
                           let haseq_sort1 =
                             let uu____2695 = is_mutual sort  in
                             if uu____2695
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
                           let uu____2702 =
                             let uu____2703 =
                               let uu____2704 =
                                 let uu____2705 =
                                   let uu____2706 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs [((fst b), None)]
                                     uu____2706 None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____2705  in
                               [uu____2704]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2703
                              in
                           uu____2702 None FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2718 -> acc
  
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2761 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2773,bs,t,uu____2776,d_lids) -> (lid, bs, t, d_lids)
    | uu____2783 -> failwith "Impossible!"  in
  match uu____2761 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2799 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2799 t  in
      let uu____2806 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2806 with
       | (bs2,t2) ->
           let ibs =
             let uu____2817 =
               let uu____2818 = FStar_Syntax_Subst.compress t2  in
               uu____2818.FStar_Syntax_Syntax.n  in
             match uu____2817 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2825) -> ibs
             | uu____2836 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2841 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2842 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2841 uu____2842  in
           let ind1 =
             let uu____2847 =
               let uu____2848 =
                 FStar_List.map
                   (fun uu____2853  ->
                      match uu____2853 with
                      | (bv,aq) ->
                          let uu____2860 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2860, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2848  in
             uu____2847 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2868 =
               let uu____2869 =
                 FStar_List.map
                   (fun uu____2874  ->
                      match uu____2874 with
                      | (bv,aq) ->
                          let uu____2881 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2881, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2869  in
             uu____2868 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2889 =
               let uu____2890 =
                 let uu____2891 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2891]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2890
                in
             uu____2889 None FStar_Range.dummyRange  in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2899,uu____2900,uu____2901,t_lid,uu____2903,uu____2904)
                      -> t_lid = lid
                  | uu____2907 -> failwith "Impossible")
               all_datas_in_the_bundle
              in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas
              in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind  in
           let fml1 =
             let uu___92_2913 = fml  in
             let uu____2914 =
               let uu____2915 =
                 let uu____2920 =
                   let uu____2921 =
                     let uu____2928 =
                       let uu____2930 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2930]  in
                     [uu____2928]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2921  in
                 (fml, uu____2920)  in
               FStar_Syntax_Syntax.Tm_meta uu____2915  in
             {
               FStar_Syntax_Syntax.n = uu____2914;
               FStar_Syntax_Syntax.tk = (uu___92_2913.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___92_2913.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___92_2913.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2942 =
                      let uu____2943 =
                        let uu____2944 =
                          let uu____2945 =
                            let uu____2946 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2946 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2945  in
                        [uu____2944]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2943
                       in
                    uu____2942 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2963 =
                      let uu____2964 =
                        let uu____2965 =
                          let uu____2966 =
                            let uu____2967 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((fst b), None)]
                              uu____2967 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2966  in
                        [uu____2965]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2964
                       in
                    uu____2963 None FStar_Range.dummyRange) bs2 fml2
              in
           FStar_Syntax_Util.mk_conj acc fml3)
  
let unoptimized_haseq_scheme :
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
                       (lid,uu____3031,uu____3032,uu____3033,uu____3034,uu____3035)
                       -> lid
                   | uu____3040 -> failwith "Impossible!") tcs
               in
            let uu____3041 =
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3049,uu____3050,uu____3051,uu____3052) ->
                  (lid, us)
              | uu____3057 -> failwith "Impossible!"  in
            match uu____3041 with
            | (lid,us) ->
                let uu____3063 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____3063 with
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
                         let uu____3081 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env1 uu____3081 fml []
                           FStar_Range.dummyRange
                          in
                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                         "haseq";
                       [se])))
  
let check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____3111 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_3121  ->
                    match uu___84_3121 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3122;
                        FStar_Syntax_Syntax.sigrng = uu____3123;
                        FStar_Syntax_Syntax.sigquals = uu____3124;
                        FStar_Syntax_Syntax.sigmeta = uu____3125;_} -> true
                    | uu____3135 -> false))
             in
          match uu____3111 with
          | (tys,datas) ->
              ((let uu____3148 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_3150  ->
                          match uu___85_3150 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3151;
                              FStar_Syntax_Syntax.sigrng = uu____3152;
                              FStar_Syntax_Syntax.sigquals = uu____3153;
                              FStar_Syntax_Syntax.sigmeta = uu____3154;_} ->
                              false
                          | uu____3163 -> true))
                   in
                if uu____3148
                then
                  let uu____3164 =
                    let uu____3165 =
                      let uu____3168 = FStar_TypeChecker_Env.get_range env
                         in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3168)
                       in
                    FStar_Errors.Error uu____3165  in
                  raise uu____3164
                else ());
               (let env0 = env  in
                let uu____3171 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3185  ->
                         match uu____3185 with
                         | (env1,all_tcs,g) ->
                             let uu____3207 = tc_tycon env1 tc  in
                             (match uu____3207 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____3224 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____3224
                                    then
                                      let uu____3225 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3225
                                    else ());
                                   (let uu____3227 =
                                      let uu____3228 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3228
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3227))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____3171 with
                | (env1,tcs,g) ->
                    let uu____3253 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3261  ->
                             match uu____3261 with
                             | (datas1,g1) ->
                                 let uu____3272 =
                                   let uu____3275 = tc_data env1 tcs  in
                                   uu____3275 se  in
                                 (match uu____3272 with
                                  | (data,g') ->
                                      let uu____3285 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____3285))) datas
                        ([], g)
                       in
                    (match uu____3253 with
                     | (datas1,g1) ->
                         let uu____3297 =
                           generalize_and_inst_within env0 g1 tcs datas1  in
                         (match uu____3297 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3314 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3314;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                }  in
                              (sig_bndle, tcs1, datas2)))))
  