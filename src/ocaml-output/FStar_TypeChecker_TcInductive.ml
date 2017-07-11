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
                         let uu____73 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____73 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____86 =
                                let uu____89 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____89 with
                                | (t1,uu____96,g) ->
                                    let uu____98 =
                                      let uu____99 =
                                        let uu____100 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____100 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____99 in
                                    (t1, uu____98) in
                              (match uu____86 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____109 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____109 in
                                   let uu____111 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____111 with
                                    | (t_type,u) ->
                                        ((let uu____121 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____121);
                                         (let t_tc =
                                            let uu____124 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____124 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          let uu____131 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____131,
                                            (let uu___86_135 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___86_135.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___86_135.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___86_135.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___86_135.FStar_Syntax_Syntax.sigattrs)
                                             }), u, guard)))))))))
      | uu____139 -> failwith "impossible"
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
            let uu____179 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____206  ->
                     match uu____206 with
                     | (se1,u_tc) ->
                         let uu____215 =
                           let uu____216 =
                             let uu____217 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____217 in
                           FStar_Ident.lid_equals tc_lid uu____216 in
                         if uu____215
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____227,uu____228,tps,uu____230,uu____231,uu____232)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____254  ->
                                          match uu____254 with
                                          | (x,uu____261) ->
                                              (x,
                                                (FStar_Pervasives_Native.Some
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____264 =
                                  let uu____268 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____268, tps2, u_tc) in
                                FStar_Pervasives_Native.Some uu____264
                            | uu____272 -> failwith "Impossible")
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
            (match uu____179 with
             | (env1,tps,u_tc) ->
                 let uu____311 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____319 =
                     let uu____320 = FStar_Syntax_Subst.compress t1 in
                     uu____320.FStar_Syntax_Syntax.n in
                   match uu____319 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____338 = FStar_Util.first_N ntps bs in
                       (match uu____338 with
                        | (uu____355,bs') ->
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_arrow (bs', res))
                                FStar_Pervasives_Native.None
                                t1.FStar_Syntax_Syntax.pos in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____388  ->
                                        match uu____388 with
                                        | (x,uu____392) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x))) in
                            let uu____393 =
                              FStar_Syntax_Subst.subst subst1 t2 in
                            FStar_Syntax_Util.arrow_formals uu____393)
                   | uu____394 -> ([], t1) in
                 (match uu____311 with
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
                                   | FStar_Syntax_Syntax.Tm_type uu____438 ->
                                       ()
                                   | ty ->
                                       let uu____440 =
                                         let uu____441 =
                                           let uu____444 =
                                             let uu____445 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1 in
                                             let uu____446 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____445 uu____446 in
                                           (uu____444,
                                             (se.FStar_Syntax_Syntax.sigrng)) in
                                         FStar_Errors.Error uu____441 in
                                       raise uu____440);
                                  (let uu____447 =
                                     FStar_Syntax_Util.head_and_args result1 in
                                   match uu____447 with
                                   | (head1,uu____458) ->
                                       ((let uu____470 =
                                           let uu____471 =
                                             FStar_Syntax_Subst.compress
                                               head1 in
                                           uu____471.FStar_Syntax_Syntax.n in
                                         match uu____470 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____474 ->
                                             let uu____475 =
                                               let uu____476 =
                                                 let uu____479 =
                                                   let uu____480 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid in
                                                   let uu____481 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1 in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____480 uu____481 in
                                                 (uu____479,
                                                   (se.FStar_Syntax_Syntax.sigrng)) in
                                               FStar_Errors.Error uu____476 in
                                             raise uu____475);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____492  ->
                                                  fun u_x  ->
                                                    match uu____492 with
                                                    | (x,uu____497) ->
                                                        let uu____498 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____498)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us in
                                         let t1 =
                                           let uu____501 =
                                             let uu____505 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____522  ->
                                                       match uu____522 with
                                                       | (x,uu____529) ->
                                                           (x,
                                                             (FStar_Pervasives_Native.Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true))))) in
                                             FStar_List.append uu____505
                                               arguments1 in
                                           let uu____534 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1 in
                                           FStar_Syntax_Util.arrow uu____501
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
                                               (uu___87_537.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___87_537.FStar_Syntax_Syntax.sigattrs)
                                           }), g))))))))))
        | uu____541 -> failwith "impossible"
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
            let uu___88_581 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_581.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_581.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_581.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____587 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____587
           then
             let uu____588 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____588
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____609  ->
                     match uu____609 with
                     | (se,uu____613) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____614,uu____615,tps,k,uu____618,uu____619)
                              ->
                              let uu____624 =
                                let uu____625 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____625 in
                              FStar_Syntax_Syntax.null_binder uu____624
                          | uu____629 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____642,uu____643,t,uu____645,uu____646,uu____647)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____650 -> failwith "Impossible")) in
           let t =
             let uu____653 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____653 in
           (let uu____656 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____656
            then
              let uu____657 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____657
            else ());
           (let uu____659 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____659 with
            | (uvs,t1) ->
                ((let uu____669 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____669
                  then
                    let uu____670 =
                      let uu____671 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____671
                        (FStar_String.concat ", ") in
                    let uu____678 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____670 uu____678
                  else ());
                 (let uu____680 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____680 with
                  | (uvs1,t2) ->
                      let uu____689 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____689 with
                       | (args,uu____701) ->
                           let uu____710 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____710 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____766  ->
                                       fun uu____767  ->
                                         match (uu____766, uu____767) with
                                         | ((x,uu____777),(se,uu____779)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____785,tps,uu____787,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____795 =
                                                    let uu____802 =
                                                      let uu____803 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____803.FStar_Syntax_Syntax.n in
                                                    match uu____802 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____821 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____821 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____863 ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____878 -> ([], ty) in
                                                  (match uu____795 with
                                                   | (tps1,t3) ->
                                                       let uu___89_894 = se in
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
                                                           (uu___89_894.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___89_894.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___89_894.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___89_894.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____901 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____905 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_39  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_39)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_933  ->
                                                match uu___82_933 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____938,uu____939,uu____940,uu____941,uu____942);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____943;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____944;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____945;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____946;_}
                                                    -> (tc, uvs_universes)
                                                | uu____954 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____972  ->
                                           fun d  ->
                                             match uu____972 with
                                             | (t3,uu____977) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____979,uu____980,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____987 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____987
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___90_988 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_988.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___90_988.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___90_988.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___90_988.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____990 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____1001 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____1001
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____1011 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____1011
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1021 =
      let uu____1022 = FStar_Syntax_Subst.compress t in
      uu____1022.FStar_Syntax_Syntax.n in
    match uu____1021 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1035 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1038 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1061 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1076  ->
               match uu____1076 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1096 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        FStar_Pervasives_Native.fst uu____1096 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____1061
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1191 =
             let uu____1192 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1192 in
           debug_log env uu____1191);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1195 =
              let uu____1196 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1196 in
            debug_log env uu____1195);
           (let uu____1199 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1199) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1209 =
                  let uu____1210 = FStar_Syntax_Subst.compress btype1 in
                  uu____1210.FStar_Syntax_Syntax.n in
                match uu____1209 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1224 = try_get_fv t in
                    (match uu____1224 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1236  ->
                                 match uu____1236 with
                                 | (t1,uu____1240) ->
                                     let uu____1241 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1241) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1255 =
                        let uu____1256 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1256 in
                      if uu____1255
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1266  ->
                               match uu____1266 with
                               | (b,uu____1270) ->
                                   let uu____1271 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1271) sbs)
                           &&
                           ((let uu____1276 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1276 with
                             | (uu____1279,return_type) ->
                                 let uu____1281 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1281)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1282 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1284 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1287) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1292) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1296,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1331  ->
                          match uu____1331 with
                          | (p,uu____1338,t) ->
                              let bs =
                                let uu____1346 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1346 in
                              let uu____1348 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1348 with
                               | (bs1,t1) ->
                                   let uu____1353 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1353)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1355,uu____1356)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1378 ->
                    ((let uu____1380 =
                        let uu____1381 =
                          let uu____1382 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____1383 =
                            let uu____1384 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____1384 in
                          Prims.strcat uu____1382 uu____1383 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1381 in
                      debug_log env uu____1380);
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
              (let uu____1392 =
                 let uu____1393 =
                   let uu____1394 =
                     let uu____1395 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1395 in
                   Prims.strcat ilid.FStar_Ident.str uu____1394 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1393 in
               debug_log env uu____1392);
              (let uu____1396 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1396 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1406 =
                        already_unfolded ilid args unfolded env in
                      if uu____1406
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1411 =
                            let uu____1412 =
                              let uu____1413 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1413
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1412 in
                          debug_log env uu____1411);
                         (let uu____1415 =
                            let uu____1416 = FStar_ST.read unfolded in
                            let uu____1420 =
                              let uu____1424 =
                                let uu____1431 =
                                  let uu____1436 =
                                    FStar_List.splitAt num_ibs args in
                                  FStar_Pervasives_Native.fst uu____1436 in
                                (ilid, uu____1431) in
                              [uu____1424] in
                            FStar_List.append uu____1416 uu____1420 in
                          FStar_ST.write unfolded uu____1415);
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
                  (let uu____1487 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1487 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____1503 ->
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
                         (let uu____1506 =
                            let uu____1507 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1507 in
                          debug_log env uu____1506);
                         (let uu____1508 =
                            let uu____1509 = FStar_Syntax_Subst.compress dt1 in
                            uu____1509.FStar_Syntax_Syntax.n in
                          match uu____1508 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1522 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1522 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____1549 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1549 dbs1 in
                                    let c1 =
                                      let uu____1552 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1552 c in
                                    let uu____1554 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1554 with
                                     | (args1,uu____1569) ->
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
                                           let uu____1610 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1610 c1 in
                                         ((let uu____1621 =
                                             let uu____1622 =
                                               let uu____1623 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____1624 =
                                                 let uu____1625 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____1625 in
                                               Prims.strcat uu____1623
                                                 uu____1624 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1622 in
                                           debug_log env uu____1621);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1626 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1628 =
                                  let uu____1629 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____1629.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1628
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
                   (let uu____1650 = try_get_fv t1 in
                    match uu____1650 with
                    | (fv,uu____1654) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1667 =
                      let uu____1668 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1668 in
                    debug_log env uu____1667);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____1670 =
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
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____1695 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____1694, uu____1695))) (true, env)
                        sbs1 in
                    match uu____1670 with | (b,uu____1701) -> b))
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
                          | uu____1743 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1745 =
                      let uu____1746 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1746 in
                    debug_log env uu____1745);
                   (let uu____1747 =
                      let uu____1748 = FStar_Syntax_Subst.compress dt in
                      uu____1748.FStar_Syntax_Syntax.n in
                    match uu____1747 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1750 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1753) ->
                        let dbs1 =
                          let uu____1766 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          FStar_Pervasives_Native.snd uu____1766 in
                        let dbs2 =
                          let uu____1790 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1790 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____1794 =
                            let uu____1795 =
                              let uu____1796 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____1796 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1795 in
                          debug_log env uu____1794);
                         (let uu____1805 =
                            FStar_List.fold_left
                              (fun uu____1816  ->
                                 fun b  ->
                                   match uu____1816 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1829 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____1830 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____1829, uu____1830)))
                              (true, env) dbs3 in
                          match uu____1805 with | (b,uu____1836) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1837,uu____1838) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1850 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____1870 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1880,uu____1881,uu____1882) -> (lid, us, bs)
        | uu____1887 -> failwith "Impossible!" in
      match uu____1870 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1894 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____1894 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____1909 =
                 let uu____1911 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 FStar_Pervasives_Native.snd uu____1911 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1919 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1919
                      unfolded_inductives env2) uu____1909)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1928,uu____1929,t,uu____1931,uu____1932,uu____1933) -> t
    | uu____1936 -> failwith "Impossible!"
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
          let uu____1957 =
            let uu____1958 = FStar_Syntax_Subst.compress dt1 in
            uu____1958.FStar_Syntax_Syntax.n in
          match uu____1957 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1961) ->
              let dbs1 =
                let uu____1974 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                FStar_Pervasives_Native.snd uu____1974 in
              let dbs2 =
                let uu____1998 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____1998 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____2011 =
                           let uu____2012 =
                             let uu____2013 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             [uu____2013] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____2012 in
                         uu____2011 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____2020 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____2020 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2028 =
                       let uu____2029 =
                         let uu____2030 =
                           let uu____2031 =
                             let uu____2032 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____2032
                               FStar_Pervasives_Native.None in
                           FStar_Syntax_Syntax.as_arg uu____2031 in
                         [uu____2030] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2029 in
                     uu____2028 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____2044 -> FStar_Syntax_Util.t_true
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
            let uu____2092 =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____2104,bs,t,uu____2107,d_lids) ->
                  (lid, bs, t, d_lids)
              | uu____2114 -> failwith "Impossible!" in
            match uu____2092 with
            | (lid,bs,t,d_lids) ->
                let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                let t1 =
                  let uu____2137 =
                    FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                      usubst in
                  FStar_Syntax_Subst.subst uu____2137 t in
                let uu____2147 = FStar_Syntax_Subst.open_term bs1 t1 in
                (match uu____2147 with
                 | (bs2,t2) ->
                     let ibs =
                       let uu____2165 =
                         let uu____2166 = FStar_Syntax_Subst.compress t2 in
                         uu____2166.FStar_Syntax_Syntax.n in
                       match uu____2165 with
                       | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2172) -> ibs
                       | uu____2181 -> [] in
                     let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                     let ind =
                       let uu____2186 =
                         FStar_Syntax_Syntax.fvar lid
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       let uu____2187 =
                         FStar_List.map
                           (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____2186 uu____2187 in
                     let ind1 =
                       let uu____2192 =
                         let uu____2193 =
                           FStar_List.map
                             (fun uu____2202  ->
                                match uu____2202 with
                                | (bv,aq) ->
                                    let uu____2209 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____2209, aq)) bs2 in
                         FStar_Syntax_Syntax.mk_Tm_app ind uu____2193 in
                       uu____2192 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let ind2 =
                       let uu____2216 =
                         let uu____2217 =
                           FStar_List.map
                             (fun uu____2226  ->
                                match uu____2226 with
                                | (bv,aq) ->
                                    let uu____2233 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    (uu____2233, aq)) ibs1 in
                         FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2217 in
                       uu____2216 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let haseq_ind =
                       let uu____2240 =
                         let uu____2241 =
                           let uu____2242 = FStar_Syntax_Syntax.as_arg ind2 in
                           [uu____2242] in
                         FStar_Syntax_Syntax.mk_Tm_app
                           FStar_Syntax_Util.t_haseq uu____2241 in
                       uu____2240 FStar_Pervasives_Native.None
                         FStar_Range.dummyRange in
                     let bs' =
                       FStar_List.filter
                         (fun b  ->
                            let uu____2263 = acc in
                            match uu____2263 with
                            | (uu____2271,en,uu____2273,uu____2274) ->
                                let opt =
                                  let uu____2283 =
                                    let uu____2284 =
                                      FStar_Syntax_Util.type_u () in
                                    FStar_Pervasives_Native.fst uu____2284 in
                                  FStar_TypeChecker_Rel.try_subtype' en
                                    (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    uu____2283 false in
                                (match opt with
                                 | FStar_Pervasives_Native.None  -> false
                                 | FStar_Pervasives_Native.Some uu____2287 ->
                                     true)) bs2 in
                     let haseq_bs =
                       FStar_List.fold_left
                         (fun t3  ->
                            fun b  ->
                              let uu____2294 =
                                let uu____2295 =
                                  let uu____2296 =
                                    let uu____2297 =
                                      let uu____2298 =
                                        FStar_Syntax_Syntax.bv_to_name
                                          (FStar_Pervasives_Native.fst b) in
                                      FStar_Syntax_Syntax.as_arg uu____2298 in
                                    [uu____2297] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.t_haseq uu____2296 in
                                uu____2295 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange in
                              FStar_Syntax_Util.mk_conj t3 uu____2294)
                         FStar_Syntax_Util.t_true bs' in
                     let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
                     let fml1 =
                       let uu___91_2306 = fml in
                       let uu____2307 =
                         let uu____2308 =
                           let uu____2312 =
                             let uu____2313 =
                               let uu____2319 =
                                 let uu____2321 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind in
                                 [uu____2321] in
                               [uu____2319] in
                             FStar_Syntax_Syntax.Meta_pattern uu____2313 in
                           (fml, uu____2312) in
                         FStar_Syntax_Syntax.Tm_meta uu____2308 in
                       {
                         FStar_Syntax_Syntax.n = uu____2307;
                         FStar_Syntax_Syntax.pos =
                           (uu___91_2306.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___91_2306.FStar_Syntax_Syntax.vars)
                       } in
                     let fml2 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____2334 =
                                let uu____2335 =
                                  let uu____2336 =
                                    let uu____2337 =
                                      let uu____2338 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____2338
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____2337 in
                                  [uu____2336] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____2335 in
                              uu____2334 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) ibs1 fml1 in
                     let fml3 =
                       FStar_List.fold_right
                         (fun b  ->
                            fun t3  ->
                              let uu____2358 =
                                let uu____2359 =
                                  let uu____2360 =
                                    let uu____2361 =
                                      let uu____2362 =
                                        FStar_Syntax_Subst.close [b] t3 in
                                      FStar_Syntax_Util.abs
                                        [((FStar_Pervasives_Native.fst b),
                                           FStar_Pervasives_Native.None)]
                                        uu____2362
                                        FStar_Pervasives_Native.None in
                                    FStar_Syntax_Syntax.as_arg uu____2361 in
                                  [uu____2360] in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.tforall uu____2359 in
                              uu____2358 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange) bs2 fml2 in
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
                     let uu____2376 = acc in
                     (match uu____2376 with
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
                                     (uu____2415,uu____2416,uu____2417,t_lid,uu____2419,uu____2420)
                                     -> t_lid = lid
                                 | uu____2423 -> failwith "Impossible")
                              all_datas_in_the_bundle in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____2430 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs2 in
                                   FStar_Syntax_Util.mk_conj acc1 uu____2430)
                              FStar_Syntax_Util.t_true t_datas in
                          let axiom_lid =
                            FStar_Ident.lid_of_ids
                              (FStar_List.append lid.FStar_Ident.ns
                                 [FStar_Ident.id_of_text
                                    (Prims.strcat
                                       (lid.FStar_Ident.ident).FStar_Ident.idText
                                       "_haseq")]) in
                          let uu____2432 =
                            FStar_Syntax_Util.mk_conj guard' guard in
                          let uu____2434 =
                            FStar_Syntax_Util.mk_conj cond' cond in
                          ((FStar_List.append l_axioms [(axiom_lid, fml3)]),
                            env2, uu____2432, uu____2434)))
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
                  (uu____2502,us,uu____2504,uu____2505,uu____2506,uu____2507)
                  -> us
              | uu____2512 -> failwith "Impossible!" in
            let uu____2513 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2513 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____2529 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2529 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2561 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____2561 with
                       | (phi1,uu____2566) ->
                           ((let uu____2568 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____2568
                             then
                               let uu____2569 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2569
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2582  ->
                                      match uu____2582 with
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
                let uu____2629 =
                  let uu____2630 = FStar_Syntax_Subst.compress t in
                  uu____2630.FStar_Syntax_Syntax.n in
                match uu____2629 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2636) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2655 = is_mutual t' in
                    if uu____2655
                    then true
                    else
                      (let uu____2657 =
                         FStar_List.map FStar_Pervasives_Native.fst args in
                       exists_mutual uu____2657)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2666) -> is_mutual t'
                | uu____2669 -> false
              and exists_mutual uu___83_2670 =
                match uu___83_2670 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____2682 =
                let uu____2683 = FStar_Syntax_Subst.compress dt1 in
                uu____2683.FStar_Syntax_Syntax.n in
              match uu____2682 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2687) ->
                  let dbs1 =
                    let uu____2700 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    FStar_Pervasives_Native.snd uu____2700 in
                  let dbs2 =
                    let uu____2724 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2724 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2739 =
                               let uu____2740 =
                                 let uu____2741 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2741] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2740 in
                             uu____2739 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____2747 = is_mutual sort in
                             if uu____2747
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2757 =
                             let uu____2758 =
                               let uu____2759 =
                                 let uu____2760 =
                                   let uu____2761 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____2761 FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.as_arg uu____2760 in
                               [uu____2759] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2758 in
                           uu____2757 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2773 -> acc
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
              let uu____2807 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____2819,bs,t,uu____2822,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____2829 -> failwith "Impossible!" in
              match uu____2807 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
                  let t1 =
                    let uu____2844 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst in
                    FStar_Syntax_Subst.subst uu____2844 t in
                  let uu____2854 = FStar_Syntax_Subst.open_term bs1 t1 in
                  (match uu____2854 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____2864 =
                           let uu____2865 = FStar_Syntax_Subst.compress t2 in
                           uu____2865.FStar_Syntax_Syntax.n in
                         match uu____2864 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2871) ->
                             ibs
                         | uu____2880 -> [] in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs in
                       let ind =
                         let uu____2885 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         let uu____2886 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____2885
                           uu____2886 in
                       let ind1 =
                         let uu____2891 =
                           let uu____2892 =
                             FStar_List.map
                               (fun uu____2901  ->
                                  match uu____2901 with
                                  | (bv,aq) ->
                                      let uu____2908 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____2908, aq)) bs2 in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____2892 in
                         uu____2891 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let ind2 =
                         let uu____2915 =
                           let uu____2916 =
                             FStar_List.map
                               (fun uu____2925  ->
                                  match uu____2925 with
                                  | (bv,aq) ->
                                      let uu____2932 =
                                        FStar_Syntax_Syntax.bv_to_name bv in
                                      (uu____2932, aq)) ibs1 in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2916 in
                         uu____2915 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let haseq_ind =
                         let uu____2939 =
                           let uu____2940 =
                             let uu____2941 = FStar_Syntax_Syntax.as_arg ind2 in
                             [uu____2941] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____2940 in
                         uu____2939 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____2956,uu____2957,uu____2958,t_lid,uu____2960,uu____2961)
                                  -> t_lid = lid
                              | uu____2964 -> failwith "Impossible")
                           all_datas_in_the_bundle in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
                       let fml1 =
                         let uu___92_2969 = fml in
                         let uu____2970 =
                           let uu____2971 =
                             let uu____2975 =
                               let uu____2976 =
                                 let uu____2982 =
                                   let uu____2984 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind in
                                   [uu____2984] in
                                 [uu____2982] in
                               FStar_Syntax_Syntax.Meta_pattern uu____2976 in
                             (fml, uu____2975) in
                           FStar_Syntax_Syntax.Tm_meta uu____2971 in
                         {
                           FStar_Syntax_Syntax.n = uu____2970;
                           FStar_Syntax_Syntax.pos =
                             (uu___92_2969.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___92_2969.FStar_Syntax_Syntax.vars)
                         } in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____2997 =
                                  let uu____2998 =
                                    let uu____2999 =
                                      let uu____3000 =
                                        let uu____3001 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____3001
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____3000 in
                                    [uu____2999] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____2998 in
                                uu____2997 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1 in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____3021 =
                                  let uu____3022 =
                                    let uu____3023 =
                                      let uu____3024 =
                                        let uu____3025 =
                                          FStar_Syntax_Subst.close [b] t3 in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____3025
                                          FStar_Pervasives_Native.None in
                                      FStar_Syntax_Syntax.as_arg uu____3024 in
                                    [uu____3023] in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____3022 in
                                uu____3021 FStar_Pervasives_Native.None
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
                       (lid,uu____3101,uu____3102,uu____3103,uu____3104,uu____3105)
                       -> lid
                   | uu____3110 -> failwith "Impossible!") tcs in
            let uu____3111 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3119,uu____3120,uu____3121,uu____3122) ->
                  (lid, us)
              | uu____3127 -> failwith "Impossible!" in
            match uu____3111 with
            | (lid,us) ->
                let uu____3133 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3133 with
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
                         let uu____3151 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____3151 fml []
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
          let uu____3185 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_3201  ->
                    match uu___84_3201 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3202;
                        FStar_Syntax_Syntax.sigrng = uu____3203;
                        FStar_Syntax_Syntax.sigquals = uu____3204;
                        FStar_Syntax_Syntax.sigmeta = uu____3205;
                        FStar_Syntax_Syntax.sigattrs = uu____3206;_} -> true
                    | uu____3217 -> false)) in
          match uu____3185 with
          | (tys,datas) ->
              ((let uu____3230 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_3238  ->
                          match uu___85_3238 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3239;
                              FStar_Syntax_Syntax.sigrng = uu____3240;
                              FStar_Syntax_Syntax.sigquals = uu____3241;
                              FStar_Syntax_Syntax.sigmeta = uu____3242;
                              FStar_Syntax_Syntax.sigattrs = uu____3243;_} ->
                              false
                          | uu____3253 -> true)) in
                if uu____3230
                then
                  let uu____3254 =
                    let uu____3255 =
                      let uu____3258 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3258) in
                    FStar_Errors.Error uu____3255 in
                  raise uu____3254
                else ());
               (let env0 = env in
                let uu____3261 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3288  ->
                         match uu____3288 with
                         | (env1,all_tcs,g) ->
                             let uu____3310 = tc_tycon env1 tc in
                             (match uu____3310 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3327 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____3327
                                    then
                                      let uu____3328 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3328
                                    else ());
                                   (let uu____3330 =
                                      let uu____3331 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3331 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3330))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3261 with
                | (env1,tcs,g) ->
                    let uu____3356 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3372  ->
                             match uu____3372 with
                             | (datas1,g1) ->
                                 let uu____3383 =
                                   let uu____3386 = tc_data env1 tcs in
                                   uu____3386 se in
                                 (match uu____3383 with
                                  | (data,g') ->
                                      let uu____3396 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____3396))) datas
                        ([], g) in
                    (match uu____3356 with
                     | (datas1,g1) ->
                         let uu____3408 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____3408 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3425 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                let uu____3426 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3425;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____3426
                                } in
                              (sig_bndle, tcs1, datas2)))))