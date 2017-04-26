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
          let uu____30 = FStar_Syntax_Subst.open_term tps k in
          (match uu____30 with
           | (tps1,k1) ->
               let uu____39 = FStar_TypeChecker_TcTerm.tc_binders env tps1 in
               (match uu____39 with
                | (tps2,env_tps,guard_params,us) ->
                    let k2 = FStar_TypeChecker_Normalize.unfold_whnf env k1 in
                    let uu____53 = FStar_Syntax_Util.arrow_formals k2 in
                    (match uu____53 with
                     | (indices,t) ->
                         let uu____77 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices in
                         (match uu____77 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____90 =
                                let uu____93 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t in
                                match uu____93 with
                                | (t1,uu____100,g) ->
                                    let uu____102 =
                                      let uu____103 =
                                        let uu____104 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____104 in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____103 in
                                    (t1, uu____102) in
                              (match uu____90 with
                               | (t1,guard) ->
                                   let k3 =
                                     let uu____114 =
                                       FStar_Syntax_Syntax.mk_Total t1 in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____114 in
                                   let uu____117 =
                                     FStar_Syntax_Util.type_u () in
                                   (match uu____117 with
                                    | (t_type,u) ->
                                        ((let uu____127 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____127);
                                         (let t_tc =
                                            let uu____131 =
                                              FStar_Syntax_Syntax.mk_Total t1 in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____131 in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2 in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps3 k3 in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None in
                                          let uu____139 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc) in
                                          (uu____139,
                                            (let uu___86_143 = s in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k4,
                                                      mutuals, data));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigqual =
                                                 (uu___86_143.FStar_Syntax_Syntax.sigqual)
                                             }), u, guard)))))))))
      | uu____147 -> failwith "impossible"
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
            let uu____184 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____198  ->
                     match uu____198 with
                     | (se1,u_tc) ->
                         let uu____207 =
                           let uu____208 =
                             let uu____209 =
                               FStar_Syntax_Util.lid_of_sigelt se1 in
                             FStar_Util.must uu____209 in
                           FStar_Ident.lid_equals tc_lid uu____208 in
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
                                                   FStar_Syntax_Syntax.imp_tag)))) in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1 in
                                let uu____253 =
                                  let uu____257 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2 in
                                  (uu____257, tps2, u_tc) in
                                Some uu____253
                            | uu____261 -> failwith "Impossible")
                         else None) in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    Prims.raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng))) in
            (match uu____184 with
             | (env1,tps,u_tc) ->
                 let uu____300 =
                   let t1 = FStar_TypeChecker_Normalize.unfold_whnf env1 t in
                   let uu____309 =
                     let uu____310 = FStar_Syntax_Subst.compress t1 in
                     uu____310.FStar_Syntax_Syntax.n in
                   match uu____309 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____332 = FStar_Util.first_N ntps bs in
                       (match uu____332 with
                        | (uu____350,bs') ->
                            let t2 =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
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
                 (match uu____300 with
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
                                       Prims.raise uu____441);
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
                                             Prims.raise uu____483);
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
                                             FStar_Syntax_Syntax.sigqual =
                                               (uu___87_537.FStar_Syntax_Syntax.sigqual)
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
          let tc_universe_vars = FStar_List.map Prims.snd tcs in
          let g1 =
            let uu___88_578 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___88_578.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___88_578.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___88_578.FStar_TypeChecker_Env.implicits)
            } in
          (let uu____584 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses") in
           if uu____584
           then
             let uu____585 = FStar_TypeChecker_Rel.guard_to_string env g1 in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____585
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____596  ->
                     match uu____596 with
                     | (se,uu____600) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____601,uu____602,tps,k,uu____605,uu____606)
                              ->
                              let uu____611 =
                                let uu____612 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____612 in
                              FStar_Syntax_Syntax.null_binder uu____611
                          | uu____619 -> failwith "Impossible"))) in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____625,uu____626,t,uu____628,uu____629,uu____630)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____633 -> failwith "Impossible")) in
           let t =
             let uu____637 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____637 in
           (let uu____641 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses") in
            if uu____641
            then
              let uu____642 =
                FStar_TypeChecker_Normalize.term_to_string env t in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____642
            else ());
           (let uu____644 = FStar_TypeChecker_Util.generalize_universes env t in
            match uu____644 with
            | (uvs,t1) ->
                ((let uu____654 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses") in
                  if uu____654
                  then
                    let uu____655 =
                      let uu____656 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText)) in
                      FStar_All.pipe_right uu____656
                        (FStar_String.concat ", ") in
                    let uu____662 = FStar_Syntax_Print.term_to_string t1 in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____655 uu____662
                  else ());
                 (let uu____664 = FStar_Syntax_Subst.open_univ_vars uvs t1 in
                  match uu____664 with
                  | (uvs1,t2) ->
                      let uu____673 = FStar_Syntax_Util.arrow_formals t2 in
                      (match uu____673 with
                       | (args,uu____686) ->
                           let uu____697 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args in
                           (match uu____697 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____734  ->
                                       fun uu____735  ->
                                         match (uu____734, uu____735) with
                                         | ((x,uu____745),(se,uu____747)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____753,tps,uu____755,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort in
                                                  let uu____763 =
                                                    let uu____771 =
                                                      let uu____772 =
                                                        FStar_Syntax_Subst.compress
                                                          ty in
                                                      uu____772.FStar_Syntax_Syntax.n in
                                                    match uu____771 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____794 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1 in
                                                        (match uu____794 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____837 ->
                                                                   let uu____841
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    uu____841
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                                                             (tps1, t3))
                                                    | uu____864 -> ([], ty) in
                                                  (match uu____763 with
                                                   | (tps1,t3) ->
                                                       let uu___89_882 = se in
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
                                                           (uu___89_882.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigqual
                                                           =
                                                           (uu___89_882.FStar_Syntax_Syntax.sigqual)
                                                       })
                                              | uu____890 ->
                                                  failwith "Impossible"))
                                    tc_types tcs in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____894 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_28  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_28)) in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___82_911  ->
                                                match uu___82_911 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____916,uu____917,uu____918,uu____919,uu____920);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____921;
                                                    FStar_Syntax_Syntax.sigqual
                                                      = uu____922;_}
                                                    -> (tc, uvs_universes)
                                                | uu____929 ->
                                                    failwith "Impossible")) in
                                      FStar_List.map2
                                        (fun uu____935  ->
                                           fun d  ->
                                             match uu____935 with
                                             | (t3,uu____940) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____942,uu____943,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____950 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort in
                                                        FStar_All.pipe_right
                                                          uu____950
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1) in
                                                      let uu___90_951 = d in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___90_951.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigqual
                                                          =
                                                          (uu___90_951.FStar_Syntax_Syntax.sigqual)
                                                      }
                                                  | uu____953 ->
                                                      failwith "Impossible"))
                                        data_types datas in
                                (tcs1, datas1)))))))
let debug_log: FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____962 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu____962
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
let ty_occurs_in:
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____970 = FStar_Syntax_Free.fvars t in
      FStar_Util.set_mem ty_lid uu____970
let try_get_fv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv* FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____979 =
      let uu____980 = FStar_Syntax_Subst.compress t in
      uu____980.FStar_Syntax_Syntax.n in
    match uu____979 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____996 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____999 -> failwith "Node is not an fvar or a Tm_uinst"
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
          let uu____1018 = FStar_ST.read unfolded in
          FStar_List.existsML
            (fun uu____1030  ->
               match uu____1030 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1050 =
                          FStar_List.splitAt (FStar_List.length l) arrghs in
                        Prims.fst uu____1050 in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) uu____1018
let rec ty_strictly_positive_in_type:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1145 =
             let uu____1146 = FStar_Syntax_Print.term_to_string btype in
             Prims.strcat "Checking strict positivity in type: " uu____1146 in
           debug_log env uu____1145);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Normalize.Beta;
               FStar_TypeChecker_Normalize.Eager_unfolding;
               FStar_TypeChecker_Normalize.UnfoldUntil
                 FStar_Syntax_Syntax.Delta_constant;
               FStar_TypeChecker_Normalize.Iota;
               FStar_TypeChecker_Normalize.Zeta;
               FStar_TypeChecker_Normalize.AllowUnboundUniverses] env btype in
           (let uu____1149 =
              let uu____1150 = FStar_Syntax_Print.term_to_string btype1 in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1150 in
            debug_log env uu____1149);
           (let uu____1151 = ty_occurs_in ty_lid btype1 in
            Prims.op_Negation uu____1151) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1153 =
                  let uu____1154 = FStar_Syntax_Subst.compress btype1 in
                  uu____1154.FStar_Syntax_Syntax.n in
                match uu____1153 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1173 = try_get_fv t in
                    (match uu____1173 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1185  ->
                                 match uu____1185 with
                                 | (t1,uu____1189) ->
                                     let uu____1190 = ty_occurs_in ty_lid t1 in
                                     Prims.op_Negation uu____1190) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1210 =
                        let uu____1211 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        Prims.op_Negation uu____1211 in
                      if uu____1210
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1217  ->
                               match uu____1217 with
                               | (b,uu____1221) ->
                                   let uu____1222 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort in
                                   Prims.op_Negation uu____1222) sbs)
                           &&
                           ((let uu____1223 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c) in
                             match uu____1223 with
                             | (uu____1226,return_type) ->
                                 let uu____1228 =
                                   FStar_TypeChecker_Env.push_binders env sbs in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1228)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1229 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1231 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1234) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1241) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1247,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1282  ->
                          match uu____1282 with
                          | (p,uu____1290,t) ->
                              let bs =
                                let uu____1300 =
                                  FStar_Syntax_Syntax.pat_bvs p in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1300 in
                              let uu____1302 =
                                FStar_Syntax_Subst.open_term bs t in
                              (match uu____1302 with
                               | (bs1,t1) ->
                                   let uu____1307 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1 in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1307)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1309,uu____1310)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1340 ->
                    ((let uu____1342 =
                        let uu____1343 =
                          let uu____1344 =
                            FStar_Syntax_Print.tag_of_term btype1 in
                          let uu____1345 =
                            let uu____1346 =
                              FStar_Syntax_Print.term_to_string btype1 in
                            Prims.strcat " and term: " uu____1346 in
                          Prims.strcat uu____1344 uu____1345 in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1343 in
                      debug_log env uu____1342);
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
              (let uu____1354 =
                 let uu____1355 =
                   let uu____1356 =
                     let uu____1357 = FStar_Syntax_Print.args_to_string args in
                     Prims.strcat " applied to arguments: " uu____1357 in
                   Prims.strcat ilid.FStar_Ident.str uu____1356 in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1355 in
               debug_log env uu____1354);
              (let uu____1358 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid in
               match uu____1358 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1368 =
                        already_unfolded ilid args unfolded env in
                      if uu____1368
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid in
                         (let uu____1373 =
                            let uu____1374 =
                              let uu____1375 =
                                FStar_Util.string_of_int num_ibs in
                              Prims.strcat uu____1375
                                ", also adding to the memo table" in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1374 in
                          debug_log env uu____1373);
                         (let uu____1377 =
                            let uu____1378 = FStar_ST.read unfolded in
                            let uu____1382 =
                              let uu____1386 =
                                let uu____1394 =
                                  let uu____1400 =
                                    FStar_List.splitAt num_ibs args in
                                  Prims.fst uu____1400 in
                                (ilid, uu____1394) in
                              [uu____1386] in
                            FStar_List.append uu____1378 uu____1382 in
                          FStar_ST.write unfolded uu____1377);
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
                  (let uu____1458 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid in
                   match uu____1458 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1470 ->
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
                         (let uu____1473 =
                            let uu____1474 =
                              FStar_Syntax_Print.term_to_string dt1 in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1474 in
                          debug_log env uu____1473);
                         (let uu____1475 =
                            let uu____1476 = FStar_Syntax_Subst.compress dt1 in
                            uu____1476.FStar_Syntax_Syntax.n in
                          match uu____1475 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1492 =
                                  FStar_List.splitAt num_ibs dbs in
                                match uu____1492 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs in
                                    let dbs2 =
                                      let uu____1519 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1519 dbs1 in
                                    let c1 =
                                      let uu____1522 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1 in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1522 c in
                                    let uu____1524 =
                                      FStar_List.splitAt num_ibs args in
                                    (match uu____1524 with
                                     | (args1,uu____1542) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((Prims.fst ib),
                                                           (Prims.fst arg))])
                                             [] ibs1 args1 in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2 in
                                         let c2 =
                                           let uu____1588 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1 in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1588 c1 in
                                         ((let uu____1596 =
                                             let uu____1597 =
                                               let uu____1598 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3 in
                                               let uu____1599 =
                                                 let uu____1600 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2 in
                                                 Prims.strcat ", and c: "
                                                   uu____1600 in
                                               Prims.strcat uu____1598
                                                 uu____1599 in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1597 in
                                           debug_log env uu____1596);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1601 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1603 =
                                  let uu____1604 =
                                    FStar_Syntax_Subst.compress dt1 in
                                  uu____1604.FStar_Syntax_Syntax.n in
                                ty_nested_positive_in_type ty_lid uu____1603
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
                   (let uu____1630 = try_get_fv t1 in
                    match uu____1630 with
                    | (fv,uu____1634) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1653 =
                      let uu____1654 =
                        FStar_Syntax_Print.binders_to_string "; " sbs in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1654 in
                    debug_log env uu____1653);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs in
                    let uu____1656 =
                      FStar_List.fold_left
                        (fun uu____1663  ->
                           fun b  ->
                             match uu____1663 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1676 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1 in
                                    let uu____1677 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b] in
                                    (uu____1676, uu____1677))) (true, env)
                        sbs1 in
                    match uu____1656 with | (b,uu____1683) -> b))
              | uu____1684 ->
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
              let uu____1703 = FStar_TypeChecker_Env.lookup_datacon env dlid in
              match uu____1703 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1715 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1717 =
                      let uu____1718 = FStar_Syntax_Print.term_to_string dt in
                      Prims.strcat "Checking data constructor type: "
                        uu____1718 in
                    debug_log env uu____1717);
                   (let uu____1719 =
                      let uu____1720 = FStar_Syntax_Subst.compress dt in
                      uu____1720.FStar_Syntax_Syntax.n in
                    match uu____1719 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1723 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1726) ->
                        let dbs1 =
                          let uu____1741 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs in
                          Prims.snd uu____1741 in
                        let dbs2 =
                          let uu____1763 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs in
                          FStar_Syntax_Subst.subst_binders uu____1763 dbs1 in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                        ((let uu____1767 =
                            let uu____1768 =
                              let uu____1769 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3) in
                              Prims.strcat uu____1769 " binders" in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1768 in
                          debug_log env uu____1767);
                         (let uu____1775 =
                            FStar_List.fold_left
                              (fun uu____1782  ->
                                 fun b  ->
                                   match uu____1782 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1795 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1 in
                                          let uu____1796 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b] in
                                          (uu____1795, uu____1796)))
                              (true, env) dbs3 in
                          match uu____1775 with | (b,uu____1802) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1803,uu____1804) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1820 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
let check_positivity:
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref [] in
      let uu____1838 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1848,uu____1849,uu____1850) -> (lid, us, bs)
        | uu____1855 -> failwith "Impossible!" in
      match uu____1838 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1862 = FStar_Syntax_Subst.univ_var_opening ty_us in
          (match uu____1862 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1 in
               let uu____1877 =
                 let uu____1879 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                 Prims.snd uu____1879 in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1885 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1 in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1885
                      unfolded_inductives env2) uu____1877)
let datacon_typ: FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1892,uu____1893,t,uu____1895,uu____1896,uu____1897) -> t
    | uu____1900 -> failwith "Impossible!"
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
          let uu____1917 =
            let uu____1918 = FStar_Syntax_Subst.compress dt1 in
            uu____1918.FStar_Syntax_Syntax.n in
          match uu____1917 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1922) ->
              let dbs1 =
                let uu____1937 =
                  FStar_List.splitAt (FStar_List.length bs) dbs in
                Prims.snd uu____1937 in
              let dbs2 =
                let uu____1959 = FStar_Syntax_Subst.opening_of_binders bs in
                FStar_Syntax_Subst.subst_binders uu____1959 dbs1 in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1968 =
                           let uu____1969 =
                             let uu____1970 =
                               FStar_Syntax_Syntax.as_arg
                                 (Prims.fst b).FStar_Syntax_Syntax.sort in
                             [uu____1970] in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1969 in
                         uu____1968 None FStar_Range.dummyRange in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
                       let haseq_b1 =
                         let uu____1977 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str in
                         FStar_TypeChecker_Util.label uu____1977 sort_range
                           haseq_b in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____1982 =
                       let uu____1983 =
                         let uu____1984 =
                           let uu____1985 =
                             let uu____1986 = FStar_Syntax_Subst.close [b] t in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               uu____1986 None in
                           FStar_Syntax_Syntax.as_arg uu____1985 in
                         [uu____1984] in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____1983 in
                     uu____1982 None FStar_Range.dummyRange) dbs3 cond
          | uu____2003 -> FStar_Syntax_Util.t_true
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2062 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2074,bs,t,uu____2077,d_lids) -> (lid, bs, t, d_lids)
    | uu____2084 -> failwith "Impossible!" in
  match uu____2062 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2109 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2109 t in
      let uu____2116 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2116 with
       | (bs2,t2) ->
           let ibs =
             let uu____2136 =
               let uu____2137 = FStar_Syntax_Subst.compress t2 in
               uu____2137.FStar_Syntax_Syntax.n in
             match uu____2136 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2144) -> ibs
             | uu____2155 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2160 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2161 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2160 uu____2161 in
           let ind1 =
             let uu____2166 =
               let uu____2167 =
                 FStar_List.map
                   (fun uu____2172  ->
                      match uu____2172 with
                      | (bv,aq) ->
                          let uu____2179 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2179, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2167 in
             uu____2166 None FStar_Range.dummyRange in
           let ind2 =
             let uu____2187 =
               let uu____2188 =
                 FStar_List.map
                   (fun uu____2193  ->
                      match uu____2193 with
                      | (bv,aq) ->
                          let uu____2200 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2200, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2188 in
             uu____2187 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2208 =
               let uu____2209 =
                 let uu____2210 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2210] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2209 in
             uu____2208 None FStar_Range.dummyRange in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2224 = acc in
                  match uu____2224 with
                  | (uu____2232,en,uu____2234,uu____2235) ->
                      let opt =
                        let uu____2244 =
                          let uu____2245 = FStar_Syntax_Util.type_u () in
                          Prims.fst uu____2245 in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort uu____2244
                          false in
                      (match opt with
                       | None  -> false
                       | Some uu____2248 -> true)) bs2 in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2252 =
                      let uu____2253 =
                        let uu____2254 =
                          let uu____2255 =
                            let uu____2256 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst b) in
                            FStar_Syntax_Syntax.as_arg uu____2256 in
                          [uu____2255] in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2254 in
                      uu____2253 None FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_conj t3 uu____2252)
               FStar_Syntax_Util.t_true bs' in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind in
           let fml1 =
             let uu___91_2267 = fml in
             let uu____2270 =
               let uu____2271 =
                 let uu____2276 =
                   let uu____2277 =
                     let uu____2284 =
                       let uu____2286 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2286] in
                     [uu____2284] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2277 in
                 (fml, uu____2276) in
               FStar_Syntax_Syntax.Tm_meta uu____2271 in
             {
               FStar_Syntax_Syntax.n = uu____2270;
               FStar_Syntax_Syntax.tk = (uu___91_2267.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___91_2267.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___91_2267.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2300 =
                      let uu____2301 =
                        let uu____2302 =
                          let uu____2303 =
                            let uu____2304 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2304 None in
                          FStar_Syntax_Syntax.as_arg uu____2303 in
                        [uu____2302] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2301 in
                    uu____2300 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2326 =
                      let uu____2327 =
                        let uu____2328 =
                          let uu____2329 =
                            let uu____2330 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2330 None in
                          FStar_Syntax_Syntax.as_arg uu____2329 in
                        [uu____2328] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2327 in
                    uu____2326 None FStar_Range.dummyRange) bs2 fml2 in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3 in
           let uu____2350 = acc in
           (match uu____2350 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2 in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1 in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2384,uu____2385,uu____2386,t_lid,uu____2388,uu____2389)
                           -> t_lid = lid
                       | uu____2392 -> failwith "Impossible")
                    all_datas_in_the_bundle in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2396 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2 in
                         FStar_Syntax_Util.mk_conj acc1 uu____2396)
                    FStar_Syntax_Util.t_true t_datas in
                let axiom_lid =
                  FStar_Ident.lid_of_ids
                    (FStar_List.append lid.FStar_Ident.ns
                       [FStar_Ident.id_of_text
                          (Prims.strcat
                             (lid.FStar_Ident.ident).FStar_Ident.idText
                             "_haseq")]) in
                let uu____2398 = FStar_Syntax_Util.mk_conj guard' guard in
                let uu____2401 = FStar_Syntax_Util.mk_conj cond' cond in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2398, uu____2401)))
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
                  (uu____2467,us,uu____2469,uu____2470,uu____2471,uu____2472)
                  -> us
              | uu____2477 -> failwith "Impossible!" in
            let uu____2478 = FStar_Syntax_Subst.univ_var_opening us in
            match uu____2478 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                  let uu____2494 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs in
                  match uu____2494 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond in
                      let uu____2528 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi in
                      (match uu____2528 with
                       | (phi1,uu____2533) ->
                           ((let uu____2535 =
                               FStar_TypeChecker_Env.should_verify env2 in
                             if uu____2535
                             then
                               let uu____2536 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1) in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2536
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2544  ->
                                      match uu____2544 with
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
                let uu____2587 =
                  let uu____2588 = FStar_Syntax_Subst.compress t in
                  uu____2588.FStar_Syntax_Syntax.n in
                match uu____2587 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2598) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2625 = is_mutual t' in
                    if uu____2625
                    then true
                    else
                      (let uu____2627 = FStar_List.map Prims.fst args in
                       exists_mutual uu____2627)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2640) -> is_mutual t'
                | uu____2645 -> false
              and exists_mutual uu___83_2646 =
                match uu___83_2646 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1) in
              let dt = datacon_typ data in
              let dt1 = FStar_Syntax_Subst.subst usubst dt in
              let uu____2663 =
                let uu____2664 = FStar_Syntax_Subst.compress dt1 in
                uu____2664.FStar_Syntax_Syntax.n in
              match uu____2663 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2670) ->
                  let dbs1 =
                    let uu____2685 =
                      FStar_List.splitAt (FStar_List.length bs) dbs in
                    Prims.snd uu____2685 in
                  let dbs2 =
                    let uu____2707 = FStar_Syntax_Subst.opening_of_binders bs in
                    FStar_Syntax_Subst.subst_binders uu____2707 dbs1 in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2 in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort in
                           let haseq_sort =
                             let uu____2719 =
                               let uu____2720 =
                                 let uu____2721 =
                                   FStar_Syntax_Syntax.as_arg
                                     (Prims.fst b).FStar_Syntax_Syntax.sort in
                                 [uu____2721] in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2720 in
                             uu____2719 None FStar_Range.dummyRange in
                           let haseq_sort1 =
                             let uu____2729 = is_mutual sort in
                             if uu____2729
                             then
                               FStar_Syntax_Util.mk_imp haseq_ind haseq_sort
                             else haseq_sort in
                           FStar_Syntax_Util.mk_conj t haseq_sort1)
                      FStar_Syntax_Util.t_true dbs3 in
                  let cond1 =
                    FStar_List.fold_right
                      (fun b  ->
                         fun t  ->
                           let uu____2738 =
                             let uu____2739 =
                               let uu____2740 =
                                 let uu____2741 =
                                   let uu____2742 =
                                     FStar_Syntax_Subst.close [b] t in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] uu____2742 None in
                                 FStar_Syntax_Syntax.as_arg uu____2741 in
                               [uu____2740] in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2739 in
                           uu____2738 None FStar_Range.dummyRange) dbs3 cond in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2759 -> acc
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2802 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2814,bs,t,uu____2817,d_lids) -> (lid, bs, t, d_lids)
    | uu____2824 -> failwith "Impossible!" in
  match uu____2802 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs in
      let t1 =
        let uu____2840 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst in
        FStar_Syntax_Subst.subst uu____2840 t in
      let uu____2847 = FStar_Syntax_Subst.open_term bs1 t1 in
      (match uu____2847 with
       | (bs2,t2) ->
           let ibs =
             let uu____2858 =
               let uu____2859 = FStar_Syntax_Subst.compress t2 in
               uu____2859.FStar_Syntax_Syntax.n in
             match uu____2858 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2866) -> ibs
             | uu____2877 -> [] in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs in
           let ind =
             let uu____2882 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____2883 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2882 uu____2883 in
           let ind1 =
             let uu____2888 =
               let uu____2889 =
                 FStar_List.map
                   (fun uu____2894  ->
                      match uu____2894 with
                      | (bv,aq) ->
                          let uu____2901 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2901, aq)) bs2 in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2889 in
             uu____2888 None FStar_Range.dummyRange in
           let ind2 =
             let uu____2909 =
               let uu____2910 =
                 FStar_List.map
                   (fun uu____2915  ->
                      match uu____2915 with
                      | (bv,aq) ->
                          let uu____2922 = FStar_Syntax_Syntax.bv_to_name bv in
                          (uu____2922, aq)) ibs1 in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2910 in
             uu____2909 None FStar_Range.dummyRange in
           let haseq_ind =
             let uu____2930 =
               let uu____2931 =
                 let uu____2932 = FStar_Syntax_Syntax.as_arg ind2 in
                 [uu____2932] in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2931 in
             uu____2930 None FStar_Range.dummyRange in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2940,uu____2941,uu____2942,t_lid,uu____2944,uu____2945)
                      -> t_lid = lid
                  | uu____2948 -> failwith "Impossible")
               all_datas_in_the_bundle in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind in
           let fml1 =
             let uu___92_2956 = fml in
             let uu____2959 =
               let uu____2960 =
                 let uu____2965 =
                   let uu____2966 =
                     let uu____2973 =
                       let uu____2975 = FStar_Syntax_Syntax.as_arg haseq_ind in
                       [uu____2975] in
                     [uu____2973] in
                   FStar_Syntax_Syntax.Meta_pattern uu____2966 in
                 (fml, uu____2965) in
               FStar_Syntax_Syntax.Tm_meta uu____2960 in
             {
               FStar_Syntax_Syntax.n = uu____2959;
               FStar_Syntax_Syntax.tk = (uu___92_2956.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___92_2956.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___92_2956.FStar_Syntax_Syntax.vars)
             } in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2989 =
                      let uu____2990 =
                        let uu____2991 =
                          let uu____2992 =
                            let uu____2993 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2993 None in
                          FStar_Syntax_Syntax.as_arg uu____2992 in
                        [uu____2991] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2990 in
                    uu____2989 None FStar_Range.dummyRange) ibs1 fml1 in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3015 =
                      let uu____3016 =
                        let uu____3017 =
                          let uu____3018 =
                            let uu____3019 = FStar_Syntax_Subst.close [b] t3 in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____3019 None in
                          FStar_Syntax_Syntax.as_arg uu____3018 in
                        [uu____3017] in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3016 in
                    uu____3015 None FStar_Range.dummyRange) bs2 fml2 in
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
                       (lid,uu____3088,uu____3089,uu____3090,uu____3091,uu____3092)
                       -> lid
                   | uu____3097 -> failwith "Impossible!") tcs in
            let uu____3098 =
              let ty = FStar_List.hd tcs in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3106,uu____3107,uu____3108,uu____3109) ->
                  (lid, us)
              | uu____3114 -> failwith "Impossible!" in
            match uu____3098 with
            | (lid,us) ->
                let uu____3120 = FStar_Syntax_Subst.univ_var_opening us in
                (match uu____3120 with
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
                         let uu____3138 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")]) in
                         tc_assume env1 uu____3138 fml []
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
          let uu____3168 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___84_3178  ->
                    match uu___84_3178 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3179;
                        FStar_Syntax_Syntax.sigrng = uu____3180;
                        FStar_Syntax_Syntax.sigqual = uu____3181;_} -> true
                    | uu____3191 -> false)) in
          match uu____3168 with
          | (tys,datas) ->
              ((let uu____3204 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___85_3206  ->
                          match uu___85_3206 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3207;
                              FStar_Syntax_Syntax.sigrng = uu____3208;
                              FStar_Syntax_Syntax.sigqual = uu____3209;_} ->
                              false
                          | uu____3218 -> true)) in
                if uu____3204
                then
                  let uu____3219 =
                    let uu____3220 =
                      let uu____3223 = FStar_TypeChecker_Env.get_range env in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3223) in
                    FStar_Errors.Error uu____3220 in
                  Prims.raise uu____3219
                else ());
               (let env0 = env in
                let uu____3226 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3240  ->
                         match uu____3240 with
                         | (env1,all_tcs,g) ->
                             let uu____3262 = tc_tycon env1 tc in
                             (match uu____3262 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u in
                                  ((let uu____3279 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low in
                                    if uu____3279
                                    then
                                      let uu____3280 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1 in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3280
                                    else ());
                                   (let uu____3282 =
                                      let uu____3283 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g' in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3283 in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3282))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard) in
                match uu____3226 with
                | (env1,tcs,g) ->
                    let uu____3308 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3316  ->
                             match uu____3316 with
                             | (datas1,g1) ->
                                 let uu____3327 =
                                   let uu____3330 = tc_data env1 tcs in
                                   uu____3330 se in
                                 (match uu____3327 with
                                  | (data,g') ->
                                      let uu____3340 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g' in
                                      ((data :: datas1), uu____3340))) datas
                        ([], g) in
                    (match uu____3308 with
                     | (datas1,g1) ->
                         let uu____3352 =
                           generalize_and_inst_within env0 g1 tcs datas1 in
                         (match uu____3352 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3369 =
                                  FStar_TypeChecker_Env.get_range env0 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3369;
                                  FStar_Syntax_Syntax.sigqual = quals
                                } in
                              (sig_bndle, tcs1, datas2)))))