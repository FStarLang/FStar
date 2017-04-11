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
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tc,uvs,tps,k,mutuals,data,quals) ->
          let uu____33 = FStar_Syntax_Subst.open_term tps k  in
          (match uu____33 with
           | (tps1,k1) ->
               let uu____42 = FStar_TypeChecker_TcTerm.tc_binders env tps1
                  in
               (match uu____42 with
                | (tps2,env_tps,guard_params,us) ->
                    let uu____55 = FStar_Syntax_Util.arrow_formals k1  in
                    (match uu____55 with
                     | (indices,t) ->
                         let uu____79 =
                           FStar_TypeChecker_TcTerm.tc_binders env_tps
                             indices
                            in
                         (match uu____79 with
                          | (indices1,env',guard_indices,us') ->
                              let uu____92 =
                                let uu____95 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env' t
                                   in
                                match uu____95 with
                                | (t1,uu____102,g) ->
                                    let uu____104 =
                                      let uu____105 =
                                        let uu____106 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard_indices g
                                           in
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard_params uu____106
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env' uu____105
                                       in
                                    (t1, uu____104)
                                 in
                              (match uu____92 with
                               | (t1,guard) ->
                                   let k2 =
                                     let uu____116 =
                                       FStar_Syntax_Syntax.mk_Total t1  in
                                     FStar_Syntax_Util.arrow indices1
                                       uu____116
                                      in
                                   let uu____119 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____119 with
                                    | (t_type,u) ->
                                        ((let uu____129 =
                                            FStar_TypeChecker_Rel.teq env' t1
                                              t_type
                                             in
                                          FStar_TypeChecker_Rel.force_trivial_guard
                                            env' uu____129);
                                         (let t_tc =
                                            let uu____133 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_Syntax_Util.arrow
                                              (FStar_List.append tps2
                                                 indices1) uu____133
                                             in
                                          let tps3 =
                                            FStar_Syntax_Subst.close_binders
                                              tps2
                                             in
                                          let k3 =
                                            FStar_Syntax_Subst.close tps3 k2
                                             in
                                          let fv_tc =
                                            FStar_Syntax_Syntax.lid_as_fv tc
                                              FStar_Syntax_Syntax.Delta_constant
                                              None
                                             in
                                          let uu____141 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env (FStar_Util.Inr fv_tc)
                                              ([], t_tc)
                                             in
                                          (uu____141,
                                            (let uu___81_145 = s  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tc, [], tps3, k3,
                                                      mutuals, data, quals));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___81_145.FStar_Syntax_Syntax.sigrng)
                                             }), u, guard)))))))))
      | uu____150 -> failwith "impossible"
  
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
        | FStar_Syntax_Syntax.Sig_datacon
            (c,_uvs,t,tc_lid,ntps,quals,_mutual_tcs) ->
            let uu____190 =
              let tps_u_opt =
                FStar_Util.find_map tcs
                  (fun uu____204  ->
                     match uu____204 with
                     | (se1,u_tc) ->
                         let uu____213 =
                           let uu____214 =
                             let uu____215 =
                               FStar_Syntax_Util.lid_of_sigelt se1  in
                             FStar_Util.must uu____215  in
                           FStar_Ident.lid_equals tc_lid uu____214  in
                         if uu____213
                         then
                           (match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (uu____225,uu____226,tps,uu____228,uu____229,uu____230,uu____231)
                                ->
                                let tps1 =
                                  FStar_All.pipe_right tps
                                    (FStar_List.map
                                       (fun uu____252  ->
                                          match uu____252 with
                                          | (x,uu____259) ->
                                              (x,
                                                (Some
                                                   FStar_Syntax_Syntax.imp_tag))))
                                   in
                                let tps2 =
                                  FStar_Syntax_Subst.open_binders tps1  in
                                let uu____262 =
                                  let uu____266 =
                                    FStar_TypeChecker_Env.push_binders env
                                      tps2
                                     in
                                  (uu____266, tps2, u_tc)  in
                                Some uu____262
                            | uu____270 -> failwith "Impossible")
                         else None)
                 in
              match tps_u_opt with
              | Some x -> x
              | None  ->
                  if FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid
                  then (env, [], FStar_Syntax_Syntax.U_zero)
                  else
                    Prims.raise
                      (FStar_Errors.Error
                         ("Unexpected data constructor",
                           (se.FStar_Syntax_Syntax.sigrng)))
               in
            (match uu____190 with
             | (env1,tps,u_tc) ->
                 let uu____309 =
                   let uu____317 =
                     let uu____318 = FStar_Syntax_Subst.compress t  in
                     uu____318.FStar_Syntax_Syntax.n  in
                   match uu____317 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                       let uu____340 = FStar_Util.first_N ntps bs  in
                       (match uu____340 with
                        | (uu____358,bs') ->
                            let t1 =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_arrow (bs', res)))
                                None t.FStar_Syntax_Syntax.pos
                               in
                            let subst1 =
                              FStar_All.pipe_right tps
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____394  ->
                                        match uu____394 with
                                        | (x,uu____398) ->
                                            FStar_Syntax_Syntax.DB
                                              ((ntps -
                                                  ((Prims.parse_int "1") + i)),
                                                x)))
                               in
                            let uu____399 =
                              FStar_Syntax_Subst.subst subst1 t1  in
                            FStar_Syntax_Util.arrow_formals uu____399)
                   | uu____400 -> ([], t)  in
                 (match uu____309 with
                  | (arguments,result) ->
                      ((let uu____421 =
                          FStar_TypeChecker_Env.debug env1 FStar_Options.Low
                           in
                        if uu____421
                        then
                          let uu____422 = FStar_Syntax_Print.lid_to_string c
                             in
                          let uu____423 =
                            FStar_Syntax_Print.binders_to_string "->"
                              arguments
                             in
                          let uu____424 =
                            FStar_Syntax_Print.term_to_string result  in
                          FStar_Util.print3
                            "Checking datacon  %s : %s -> %s \n" uu____422
                            uu____423 uu____424
                        else ());
                       (let uu____426 =
                          FStar_TypeChecker_TcTerm.tc_tparams env1 arguments
                           in
                        match uu____426 with
                        | (arguments1,env',us) ->
                            let uu____435 =
                              FStar_TypeChecker_TcTerm.tc_trivial_guard env'
                                result
                               in
                            (match uu____435 with
                             | (result1,res_lcomp) ->
                                 ((let uu____443 =
                                     let uu____444 =
                                       FStar_Syntax_Subst.compress
                                         res_lcomp.FStar_Syntax_Syntax.res_typ
                                        in
                                     uu____444.FStar_Syntax_Syntax.n  in
                                   match uu____443 with
                                   | FStar_Syntax_Syntax.Tm_type uu____447 ->
                                       ()
                                   | ty ->
                                       let uu____449 =
                                         let uu____450 =
                                           let uu____453 =
                                             let uu____454 =
                                               FStar_Syntax_Print.term_to_string
                                                 result1
                                                in
                                             let uu____455 =
                                               FStar_Syntax_Print.term_to_string
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_Util.format2
                                               "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                               uu____454 uu____455
                                              in
                                           (uu____453,
                                             (se.FStar_Syntax_Syntax.sigrng))
                                            in
                                         FStar_Errors.Error uu____450  in
                                       Prims.raise uu____449);
                                  (let uu____456 =
                                     FStar_Syntax_Util.head_and_args result1
                                      in
                                   match uu____456 with
                                   | (head1,uu____469) ->
                                       ((let uu____485 =
                                           let uu____486 =
                                             FStar_Syntax_Subst.compress
                                               head1
                                              in
                                           uu____486.FStar_Syntax_Syntax.n
                                            in
                                         match uu____485 with
                                         | FStar_Syntax_Syntax.Tm_fvar fv
                                             when
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               tc_lid
                                             -> ()
                                         | uu____490 ->
                                             let uu____491 =
                                               let uu____492 =
                                                 let uu____495 =
                                                   let uu____496 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       tc_lid
                                                      in
                                                   let uu____497 =
                                                     FStar_Syntax_Print.term_to_string
                                                       head1
                                                      in
                                                   FStar_Util.format2
                                                     "Expected a constructor of type %s; got %s"
                                                     uu____496 uu____497
                                                    in
                                                 (uu____495,
                                                   (se.FStar_Syntax_Syntax.sigrng))
                                                  in
                                               FStar_Errors.Error uu____492
                                                in
                                             Prims.raise uu____491);
                                        (let g =
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun uu____502  ->
                                                  fun u_x  ->
                                                    match uu____502 with
                                                    | (x,uu____507) ->
                                                        let uu____508 =
                                                          FStar_TypeChecker_Rel.universe_inequality
                                                            u_x u_tc
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g uu____508)
                                             FStar_TypeChecker_Rel.trivial_guard
                                             arguments1 us
                                            in
                                         let t1 =
                                           let uu____512 =
                                             let uu____516 =
                                               FStar_All.pipe_right tps
                                                 (FStar_List.map
                                                    (fun uu____530  ->
                                                       match uu____530 with
                                                       | (x,uu____537) ->
                                                           (x,
                                                             (Some
                                                                (FStar_Syntax_Syntax.Implicit
                                                                   true)))))
                                                in
                                             FStar_List.append uu____516
                                               arguments1
                                              in
                                           let uu____542 =
                                             FStar_Syntax_Syntax.mk_Total
                                               result1
                                              in
                                           FStar_Syntax_Util.arrow uu____512
                                             uu____542
                                            in
                                         ((let uu___82_545 = se  in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (FStar_Syntax_Syntax.Sig_datacon
                                                  (c, [], t1, tc_lid, ntps,
                                                    quals, []));
                                             FStar_Syntax_Syntax.sigrng =
                                               (uu___82_545.FStar_Syntax_Syntax.sigrng)
                                           }), g))))))))))
        | uu____551 -> failwith "impossible"
  
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
          let tc_universe_vars = FStar_List.map Prims.snd tcs  in
          let g1 =
            let uu___83_587 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___83_587.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___83_587.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (Prims.snd g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___83_587.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____593 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____593
           then
             let uu____594 = FStar_TypeChecker_Rel.guard_to_string env g1  in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____594
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____605  ->
                     match uu____605 with
                     | (se,uu____609) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____610,uu____611,tps,k,uu____614,uu____615,uu____616)
                              ->
                              let uu____623 =
                                let uu____624 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____624
                                 in
                              FStar_Syntax_Syntax.null_binder uu____623
                          | uu____631 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____637,uu____638,t,uu____640,uu____641,uu____642,uu____643)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____648 -> failwith "Impossible"))
              in
           let t =
             let uu____652 =
               FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit
                in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____652
              in
           (let uu____656 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____656
            then
              let uu____657 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____657
            else ());
           (let uu____659 = FStar_TypeChecker_Util.generalize_universes env t
               in
            match uu____659 with
            | (uvs,t1) ->
                ((let uu____669 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____669
                  then
                    let uu____670 =
                      let uu____671 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____671
                        (FStar_String.concat ", ")
                       in
                    let uu____677 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____670 uu____677
                  else ());
                 (let uu____679 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____679 with
                  | (uvs1,t2) ->
                      let uu____688 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____688 with
                       | (args,uu____701) ->
                           let uu____712 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____712 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____749  ->
                                       fun uu____750  ->
                                         match (uu____749, uu____750) with
                                         | ((x,uu____760),(se,uu____762)) ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____768,tps,uu____770,mutuals,datas1,quals)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____781 =
                                                    let uu____789 =
                                                      let uu____790 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____790.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____789 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____812 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____812 with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____855 ->
                                                                   let uu____859
                                                                    =
                                                                    FStar_ST.read
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk
                                                                     in
                                                                   (FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c)))
                                                                    uu____859
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____882 -> ([], ty)
                                                     in
                                                  (match uu____781 with
                                                   | (tps1,t3) ->
                                                       let uu___84_900 = se
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.sigel
                                                           =
                                                           (FStar_Syntax_Syntax.Sig_inductive_typ
                                                              (tc, uvs1,
                                                                tps1, t3,
                                                                mutuals,
                                                                datas1,
                                                                quals));
                                                         FStar_Syntax_Syntax.sigrng
                                                           =
                                                           (uu___84_900.FStar_Syntax_Syntax.sigrng)
                                                       })
                                              | uu____909 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____913 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_28  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_28))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___77_930  ->
                                                match uu___77_930 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____935,uu____936,uu____937,uu____938,uu____939,uu____940);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____941;_}
                                                    -> (tc, uvs_universes)
                                                | uu____949 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____955  ->
                                           fun d  ->
                                             match uu____955 with
                                             | (t3,uu____960) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____962,uu____963,tc,ntps,quals,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____973 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____973
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___85_974 = d  in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               quals,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___85_974.FStar_Syntax_Syntax.sigrng)
                                                      }
                                                  | uu____977 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> Prims.unit =
  fun env  ->
    fun s  ->
      let uu____986 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____986
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun ty_lid  ->
    fun t  ->
      let uu____994 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____994
  
let try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
  =
  fun t  ->
    let uu____1003 =
      let uu____1004 = FStar_Syntax_Subst.compress t  in
      uu____1004.FStar_Syntax_Syntax.n  in
    match uu____1003 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____1020 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____1023 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____1042 = FStar_ST.read unfolded  in
          FStar_List.existsML
            (fun uu____1054  ->
               match uu____1054 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____1074 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        Prims.fst uu____1074  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt env
                                    (Prims.fst a) (Prims.fst a'))) true args
                        l)) uu____1042
  
let rec ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____1169 =
             let uu____1170 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____1170
              in
           debug_log env uu____1169);
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
           (let uu____1173 =
              let uu____1174 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____1174
               in
            debug_log env uu____1173);
           (let uu____1175 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____1175) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____1177 =
                  let uu____1178 = FStar_Syntax_Subst.compress btype1  in
                  uu____1178.FStar_Syntax_Syntax.n  in
                match uu____1177 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____1197 = try_get_fv t  in
                    (match uu____1197 with
                     | (fv,us) ->
                         if
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____1209  ->
                                 match uu____1209 with
                                 | (t1,uu____1213) ->
                                     let uu____1214 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____1214) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let uu____1234 =
                        let uu____1235 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        Prims.op_Negation uu____1235  in
                      if uu____1234
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____1241  ->
                               match uu____1241 with
                               | (b,uu____1245) ->
                                   let uu____1246 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____1246) sbs)
                           &&
                           ((let uu____1247 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____1247 with
                             | (uu____1250,return_type) ->
                                 let uu____1252 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____1252)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____1253 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____1255 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____1258) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____1265) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____1271,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____1306  ->
                          match uu____1306 with
                          | (p,uu____1314,t) ->
                              let bs =
                                let uu____1324 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____1324
                                 in
                              let uu____1326 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____1326 with
                               | (bs1,t1) ->
                                   let uu____1331 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____1331)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1333,uu____1334)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____1364 ->
                    ((let uu____1366 =
                        let uu____1367 =
                          let uu____1368 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____1369 =
                            let uu____1370 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____1370  in
                          Prims.strcat uu____1368 uu____1369  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____1367
                         in
                      debug_log env uu____1366);
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
              (let uu____1378 =
                 let uu____1379 =
                   let uu____1380 =
                     let uu____1381 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____1381  in
                   Prims.strcat ilid.FStar_Ident.str uu____1380  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____1379
                  in
               debug_log env uu____1378);
              (let uu____1382 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____1382 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     (debug_log env
                        "Checking nested positivity, not an inductive, return false";
                      false)
                   else
                     (let uu____1392 =
                        already_unfolded ilid args unfolded env  in
                      if uu____1392
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____1397 =
                            let uu____1398 =
                              let uu____1399 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____1399
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____1398
                             in
                          debug_log env uu____1397);
                         (let uu____1401 =
                            let uu____1402 = FStar_ST.read unfolded  in
                            let uu____1406 =
                              let uu____1410 =
                                let uu____1418 =
                                  let uu____1424 =
                                    FStar_List.splitAt num_ibs args  in
                                  Prims.fst uu____1424  in
                                (ilid, uu____1418)  in
                              [uu____1410]  in
                            FStar_List.append uu____1402 uu____1406  in
                          FStar_ST.write unfolded uu____1401);
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
                  (let uu____1482 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____1482 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Unionfind.change u'' (Some u)
                               | uu____1494 ->
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
                         (let uu____1497 =
                            let uu____1498 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____1498
                             in
                          debug_log env uu____1497);
                         (let uu____1499 =
                            let uu____1500 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____1500.FStar_Syntax_Syntax.n  in
                          match uu____1499 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____1516 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____1516 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____1543 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1543 dbs1
                                       in
                                    let c1 =
                                      let uu____1546 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____1546 c
                                       in
                                    let uu____1548 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____1548 with
                                     | (args1,uu____1566) ->
                                         let subst1 =
                                           FStar_List.fold_left2
                                             (fun subst1  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst1
                                                      [FStar_Syntax_Syntax.NT
                                                         ((Prims.fst ib),
                                                           (Prims.fst arg))])
                                             [] ibs1 args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____1612 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____1612 c1
                                            in
                                         ((let uu____1620 =
                                             let uu____1621 =
                                               let uu____1622 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____1623 =
                                                 let uu____1624 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____1624
                                                  in
                                               Prims.strcat uu____1622
                                                 uu____1623
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____1621
                                              in
                                           debug_log env uu____1620);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____1625 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____1627 =
                                  let uu____1628 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____1628.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____1627
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
                   (let uu____1654 = try_get_fv t1  in
                    match uu____1654 with
                    | (fv,uu____1658) ->
                        if
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____1677 =
                      let uu____1678 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____1678
                       in
                    debug_log env uu____1677);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____1680 =
                      FStar_List.fold_left
                        (fun uu____1687  ->
                           fun b  ->
                             match uu____1687 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____1700 =
                                      ty_strictly_positive_in_type ty_lid
                                        (Prims.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____1701 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____1700, uu____1701))) (true, env)
                        sbs1
                       in
                    match uu____1680 with | (b,uu____1707) -> b))
              | uu____1708 ->
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
              let uu____1727 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____1727 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Unionfind.change u'' (Some u)
                          | uu____1739 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____1741 =
                      let uu____1742 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____1742
                       in
                    debug_log env uu____1741);
                   (let uu____1743 =
                      let uu____1744 = FStar_Syntax_Subst.compress dt  in
                      uu____1744.FStar_Syntax_Syntax.n  in
                    match uu____1743 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____1747 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1750) ->
                        let dbs1 =
                          let uu____1765 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          Prims.snd uu____1765  in
                        let dbs2 =
                          let uu____1787 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____1787 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____1791 =
                            let uu____1792 =
                              let uu____1793 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____1793 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____1792
                             in
                          debug_log env uu____1791);
                         (let uu____1799 =
                            FStar_List.fold_left
                              (fun uu____1806  ->
                                 fun b  ->
                                   match uu____1806 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____1819 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (Prims.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____1820 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____1819, uu____1820)))
                              (true, env) dbs3
                             in
                          match uu____1799 with | (b,uu____1826) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____1827,uu____1828) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | uu____1844 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env_t -> Prims.bool =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____1862 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____1872,uu____1873,uu____1874,uu____1875) ->
            (lid, us, bs)
        | uu____1882 -> failwith "Impossible!"  in
      match uu____1862 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____1889 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____1889 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____1904 =
                 let uu____1906 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 Prims.snd uu____1906  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____1912 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____1912
                      unfolded_inductives env2) uu____1904)
  
let datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1919,uu____1920,t,uu____1922,uu____1923,uu____1924,uu____1925)
        -> t
    | uu____1930 -> failwith "Impossible!"
  
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
          let uu____1947 =
            let uu____1948 = FStar_Syntax_Subst.compress dt1  in
            uu____1948.FStar_Syntax_Syntax.n  in
          match uu____1947 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____1952) ->
              let dbs1 =
                let uu____1967 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                Prims.snd uu____1967  in
              let dbs2 =
                let uu____1989 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____1989 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____1998 =
                           let uu____1999 =
                             let uu____2000 =
                               FStar_Syntax_Syntax.as_arg
                                 (Prims.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____2000]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____1999
                            in
                         uu____1998 None FStar_Range.dummyRange  in
                       let sort_range =
                         ((Prims.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____2007 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____2007 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____2012 =
                       let uu____2013 =
                         let uu____2014 =
                           let uu____2015 =
                             let uu____2016 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs [((Prims.fst b), None)]
                               uu____2016 None
                              in
                           FStar_Syntax_Syntax.as_arg uu____2015  in
                         [uu____2014]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____2013
                        in
                     uu____2012 None FStar_Range.dummyRange) dbs3 cond
          | uu____2033 -> FStar_Syntax_Util.t_true
  
let optimized_haseq_ty all_datas_in_the_bundle usubst us acc ty =
  let uu____2092 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2104,bs,t,uu____2107,d_lids,uu____2109) ->
        (lid, bs, t, d_lids)
    | uu____2117 -> failwith "Impossible!"  in
  match uu____2092 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2142 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2142 t  in
      let uu____2149 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2149 with
       | (bs2,t2) ->
           let ibs =
             let uu____2169 =
               let uu____2170 = FStar_Syntax_Subst.compress t2  in
               uu____2170.FStar_Syntax_Syntax.n  in
             match uu____2169 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2177) -> ibs
             | uu____2188 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2193 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2194 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2193 uu____2194  in
           let ind1 =
             let uu____2199 =
               let uu____2200 =
                 FStar_List.map
                   (fun uu____2205  ->
                      match uu____2205 with
                      | (bv,aq) ->
                          let uu____2212 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2212, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2200  in
             uu____2199 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2220 =
               let uu____2221 =
                 FStar_List.map
                   (fun uu____2226  ->
                      match uu____2226 with
                      | (bv,aq) ->
                          let uu____2233 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2233, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2221  in
             uu____2220 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2241 =
               let uu____2242 =
                 let uu____2243 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2243]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2242
                in
             uu____2241 None FStar_Range.dummyRange  in
           let bs' =
             FStar_List.filter
               (fun b  ->
                  let uu____2257 = acc  in
                  match uu____2257 with
                  | (uu____2265,en,uu____2267,uu____2268) ->
                      let opt =
                        let uu____2277 =
                          let uu____2278 = FStar_Syntax_Util.type_u ()  in
                          Prims.fst uu____2278  in
                        FStar_TypeChecker_Rel.try_subtype' en
                          (Prims.fst b).FStar_Syntax_Syntax.sort uu____2277
                          false
                         in
                      (match opt with
                       | None  -> false
                       | Some uu____2281 -> true)) bs2
              in
           let haseq_bs =
             FStar_List.fold_left
               (fun t3  ->
                  fun b  ->
                    let uu____2285 =
                      let uu____2286 =
                        let uu____2287 =
                          let uu____2288 =
                            let uu____2289 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst b)
                               in
                            FStar_Syntax_Syntax.as_arg uu____2289  in
                          [uu____2288]  in
                        FStar_Syntax_Syntax.mk_Tm_app
                          FStar_Syntax_Util.t_haseq uu____2287
                         in
                      uu____2286 None FStar_Range.dummyRange  in
                    FStar_Syntax_Util.mk_conj t3 uu____2285)
               FStar_Syntax_Util.t_true bs'
              in
           let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
           let fml1 =
             let uu___86_2298 = fml  in
             let uu____2299 =
               let uu____2300 =
                 let uu____2305 =
                   let uu____2306 =
                     let uu____2313 =
                       let uu____2315 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____2315]  in
                     [uu____2313]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2306  in
                 (fml, uu____2305)  in
               FStar_Syntax_Syntax.Tm_meta uu____2300  in
             {
               FStar_Syntax_Syntax.n = uu____2299;
               FStar_Syntax_Syntax.tk = (uu___86_2298.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___86_2298.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___86_2298.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2327 =
                      let uu____2328 =
                        let uu____2329 =
                          let uu____2330 =
                            let uu____2331 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2331 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2330  in
                        [uu____2329]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2328
                       in
                    uu____2327 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____2353 =
                      let uu____2354 =
                        let uu____2355 =
                          let uu____2356 =
                            let uu____2357 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____2357 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____2356  in
                        [uu____2355]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____2354
                       in
                    uu____2353 None FStar_Range.dummyRange) bs2 fml2
              in
           let guard = FStar_Syntax_Util.mk_conj haseq_bs fml3  in
           let uu____2377 = acc  in
           (match uu____2377 with
            | (l_axioms,env,guard',cond') ->
                let env1 = FStar_TypeChecker_Env.push_binders env bs2  in
                let env2 = FStar_TypeChecker_Env.push_binders env1 ibs1  in
                let t_datas =
                  FStar_List.filter
                    (fun s  ->
                       match s.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____2411,uu____2412,uu____2413,t_lid,uu____2415,uu____2416,uu____2417)
                           -> t_lid = lid
                       | uu____2422 -> failwith "Impossible")
                    all_datas_in_the_bundle
                   in
                let cond =
                  FStar_List.fold_left
                    (fun acc1  ->
                       fun d  ->
                         let uu____2426 =
                           optimized_haseq_soundness_for_data lid d usubst
                             bs2
                            in
                         FStar_Syntax_Util.mk_conj acc1 uu____2426)
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
                let uu____2428 = FStar_Syntax_Util.mk_conj guard' guard  in
                let uu____2431 = FStar_Syntax_Util.mk_conj cond' cond  in
                ((FStar_List.append l_axioms [(axiom_lid, fml3)]), env2,
                  uu____2428, uu____2431)))
  
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
                  (uu____2497,us,uu____2499,uu____2500,uu____2501,uu____2502,uu____2503)
                  -> us
              | uu____2510 -> failwith "Impossible!"  in
            let uu____2511 = FStar_Syntax_Subst.univ_var_opening us  in
            match uu____2511 with
            | (usubst,us1) ->
                let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                   in
                ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                   "haseq";
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                   env sig_bndle;
                 (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                  let uu____2527 =
                    FStar_List.fold_left
                      (optimized_haseq_ty datas usubst us1)
                      ([], env1, FStar_Syntax_Util.t_true,
                        FStar_Syntax_Util.t_true) tcs
                     in
                  match uu____2527 with
                  | (axioms,env2,guard,cond) ->
                      let phi = FStar_Syntax_Util.mk_imp guard cond  in
                      let uu____2559 =
                        FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                         in
                      (match uu____2559 with
                       | (phi1,uu____2564) ->
                           ((let uu____2566 =
                               FStar_TypeChecker_Env.should_verify env2  in
                             if uu____2566
                             then
                               let uu____2567 =
                                 FStar_TypeChecker_Rel.guard_of_guard_formula
                                   (FStar_TypeChecker_Common.NonTrivial phi1)
                                  in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 uu____2567
                             else ());
                            (let ses =
                               FStar_List.fold_left
                                 (fun l  ->
                                    fun uu____2575  ->
                                      match uu____2575 with
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
                let uu____2618 =
                  let uu____2619 = FStar_Syntax_Subst.compress t  in
                  uu____2619.FStar_Syntax_Syntax.n  in
                match uu____2618 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____2629) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____2656 = is_mutual t'  in
                    if uu____2656
                    then true
                    else
                      (let uu____2658 = FStar_List.map Prims.fst args  in
                       exists_mutual uu____2658)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____2671) -> is_mutual t'
                | uu____2676 -> false
              
              and exists_mutual uu___78_2677 =
                match uu___78_2677 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____2694 =
                let uu____2695 = FStar_Syntax_Subst.compress dt1  in
                uu____2695.FStar_Syntax_Syntax.n  in
              match uu____2694 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____2701) ->
                  let dbs1 =
                    let uu____2716 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    Prims.snd uu____2716  in
                  let dbs2 =
                    let uu____2738 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____2738 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____2750 =
                               let uu____2751 =
                                 let uu____2752 =
                                   FStar_Syntax_Syntax.as_arg
                                     (Prims.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____2752]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____2751
                                in
                             uu____2750 None FStar_Range.dummyRange  in
                           let haseq_sort1 =
                             let uu____2758 = is_mutual sort  in
                             if uu____2758
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
                           let uu____2765 =
                             let uu____2766 =
                               let uu____2767 =
                                 let uu____2768 =
                                   let uu____2769 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((Prims.fst b), None)] uu____2769 None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____2768  in
                               [uu____2767]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____2766
                              in
                           uu____2765 None FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____2786 -> acc
  
let unoptimized_haseq_ty all_datas_in_the_bundle mutuals usubst us acc ty =
  let uu____2829 =
    match ty.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2841,bs,t,uu____2844,d_lids,uu____2846) ->
        (lid, bs, t, d_lids)
    | uu____2854 -> failwith "Impossible!"  in
  match uu____2829 with
  | (lid,bs,t,d_lids) ->
      let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
      let t1 =
        let uu____2870 =
          FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst  in
        FStar_Syntax_Subst.subst uu____2870 t  in
      let uu____2877 = FStar_Syntax_Subst.open_term bs1 t1  in
      (match uu____2877 with
       | (bs2,t2) ->
           let ibs =
             let uu____2888 =
               let uu____2889 = FStar_Syntax_Subst.compress t2  in
               uu____2889.FStar_Syntax_Syntax.n  in
             match uu____2888 with
             | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____2896) -> ibs
             | uu____2907 -> []  in
           let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
           let ind =
             let uu____2912 =
               FStar_Syntax_Syntax.fvar lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____2913 =
               FStar_List.map (fun u  -> FStar_Syntax_Syntax.U_name u) us  in
             FStar_Syntax_Syntax.mk_Tm_uinst uu____2912 uu____2913  in
           let ind1 =
             let uu____2918 =
               let uu____2919 =
                 FStar_List.map
                   (fun uu____2924  ->
                      match uu____2924 with
                      | (bv,aq) ->
                          let uu____2931 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2931, aq)) bs2
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind uu____2919  in
             uu____2918 None FStar_Range.dummyRange  in
           let ind2 =
             let uu____2939 =
               let uu____2940 =
                 FStar_List.map
                   (fun uu____2945  ->
                      match uu____2945 with
                      | (bv,aq) ->
                          let uu____2952 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (uu____2952, aq)) ibs1
                  in
               FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2940  in
             uu____2939 None FStar_Range.dummyRange  in
           let haseq_ind =
             let uu____2960 =
               let uu____2961 =
                 let uu____2962 = FStar_Syntax_Syntax.as_arg ind2  in
                 [uu____2962]  in
               FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq
                 uu____2961
                in
             uu____2960 None FStar_Range.dummyRange  in
           let t_datas =
             FStar_List.filter
               (fun s  ->
                  match s.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____2970,uu____2971,uu____2972,t_lid,uu____2974,uu____2975,uu____2976)
                      -> t_lid = lid
                  | uu____2981 -> failwith "Impossible")
               all_datas_in_the_bundle
              in
           let data_cond =
             FStar_List.fold_left
               (unoptimized_haseq_data usubst bs2 haseq_ind mutuals)
               FStar_Syntax_Util.t_true t_datas
              in
           let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind  in
           let fml1 =
             let uu___87_2987 = fml  in
             let uu____2988 =
               let uu____2989 =
                 let uu____2994 =
                   let uu____2995 =
                     let uu____3002 =
                       let uu____3004 = FStar_Syntax_Syntax.as_arg haseq_ind
                          in
                       [uu____3004]  in
                     [uu____3002]  in
                   FStar_Syntax_Syntax.Meta_pattern uu____2995  in
                 (fml, uu____2994)  in
               FStar_Syntax_Syntax.Tm_meta uu____2989  in
             {
               FStar_Syntax_Syntax.n = uu____2988;
               FStar_Syntax_Syntax.tk = (uu___87_2987.FStar_Syntax_Syntax.tk);
               FStar_Syntax_Syntax.pos =
                 (uu___87_2987.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___87_2987.FStar_Syntax_Syntax.vars)
             }  in
           let fml2 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3016 =
                      let uu____3017 =
                        let uu____3018 =
                          let uu____3019 =
                            let uu____3020 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____3020 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____3019  in
                        [uu____3018]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3017
                       in
                    uu____3016 None FStar_Range.dummyRange) ibs1 fml1
              in
           let fml3 =
             FStar_List.fold_right
               (fun b  ->
                  fun t3  ->
                    let uu____3042 =
                      let uu____3043 =
                        let uu____3044 =
                          let uu____3045 =
                            let uu____3046 = FStar_Syntax_Subst.close [b] t3
                               in
                            FStar_Syntax_Util.abs [((Prims.fst b), None)]
                              uu____3046 None
                             in
                          FStar_Syntax_Syntax.as_arg uu____3045  in
                        [uu____3044]  in
                      FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall
                        uu____3043
                       in
                    uu____3042 None FStar_Range.dummyRange) bs2 fml2
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
                       (lid,uu____3115,uu____3116,uu____3117,uu____3118,uu____3119,uu____3120)
                       -> lid
                   | uu____3127 -> failwith "Impossible!") tcs
               in
            let uu____3128 =
              let ty = FStar_List.hd tcs  in
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,us,uu____3136,uu____3137,uu____3138,uu____3139,uu____3140)
                  -> (lid, us)
              | uu____3147 -> failwith "Impossible!"  in
            match uu____3128 with
            | (lid,us) ->
                let uu____3153 = FStar_Syntax_Subst.univ_var_opening us  in
                (match uu____3153 with
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
                         let uu____3171 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append lid.FStar_Ident.ns
                                [FStar_Ident.id_of_text
                                   (Prims.strcat
                                      (lid.FStar_Ident.ident).FStar_Ident.idText
                                      "_haseq")])
                            in
                         tc_assume env1 uu____3171 fml []
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
          let uu____3201 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___79_3211  ->
                    match uu___79_3211 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____3212;
                        FStar_Syntax_Syntax.sigrng = uu____3213;_} -> true
                    | uu____3224 -> false))
             in
          match uu____3201 with
          | (tys,datas) ->
              ((let uu____3237 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___80_3239  ->
                          match uu___80_3239 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____3240;
                              FStar_Syntax_Syntax.sigrng = uu____3241;_} ->
                              false
                          | uu____3251 -> true))
                   in
                if uu____3237
                then
                  let uu____3252 =
                    let uu____3253 =
                      let uu____3256 = FStar_TypeChecker_Env.get_range env
                         in
                      ("Mutually defined type contains a non-inductive element",
                        uu____3256)
                       in
                    FStar_Errors.Error uu____3253  in
                  Prims.raise uu____3252
                else ());
               (let env0 = env  in
                let uu____3259 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____3273  ->
                         match uu____3273 with
                         | (env1,all_tcs,g) ->
                             let uu____3295 = tc_tycon env1 tc  in
                             (match uu____3295 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____3312 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____3312
                                    then
                                      let uu____3313 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____3313
                                    else ());
                                   (let uu____3315 =
                                      let uu____3316 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Rel.conj_guard g
                                        uu____3316
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____3315))))) tys
                    (env, [], FStar_TypeChecker_Rel.trivial_guard)
                   in
                match uu____3259 with
                | (env1,tcs,g) ->
                    let uu____3341 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____3349  ->
                             match uu____3349 with
                             | (datas1,g1) ->
                                 let uu____3360 =
                                   let uu____3363 = tc_data env1 tcs  in
                                   uu____3363 se  in
                                 (match uu____3360 with
                                  | (data,g') ->
                                      let uu____3373 =
                                        FStar_TypeChecker_Rel.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____3373))) datas
                        ([], g)
                       in
                    (match uu____3341 with
                     | (datas1,g1) ->
                         let uu____3385 =
                           generalize_and_inst_within env0 g1 tcs datas1  in
                         (match uu____3385 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____3402 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         quals, lids));
                                  FStar_Syntax_Syntax.sigrng = uu____3402
                                }  in
                              (sig_bndle, tcs1, datas2)))))
  