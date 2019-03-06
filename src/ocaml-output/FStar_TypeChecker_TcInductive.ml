open Prims
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.unfold_whnf'
    [FStar_TypeChecker_Env.AllowUnboundUniverses]
  
let (tc_tycon :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt *
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let env0 = env  in
          let uu____62188 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____62188 with
           | (usubst,uvs1) ->
               let uu____62215 =
                 let uu____62222 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____62223 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____62224 =
                   let uu____62225 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____62225 k  in
                 (uu____62222, uu____62223, uu____62224)  in
               (match uu____62215 with
                | (env1,tps1,k1) ->
                    let uu____62245 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____62245 with
                     | (tps2,k2) ->
                         let uu____62260 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____62260 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____62281 =
                                let uu____62300 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____62300 with
                                | (k3,uu____62326,g) ->
                                    let k4 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Exclude
                                           FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Zeta;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3
                                       in
                                    let uu____62329 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____62344 =
                                      let uu____62345 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____62345
                                       in
                                    (uu____62329, uu____62344)
                                 in
                              (match uu____62281 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____62408 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____62408
                                      in
                                   let uu____62411 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____62411 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____62429 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____62429))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____62436 =
                                              let uu____62442 =
                                                let uu____62444 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____62446 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____62444 uu____62446
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____62442)
                                               in
                                            FStar_Errors.raise_error
                                              uu____62436
                                              s.FStar_Syntax_Syntax.sigrng)
                                         else ();
                                         (let usubst1 =
                                            FStar_Syntax_Subst.univ_var_closing
                                              uvs1
                                             in
                                          let guard1 =
                                            FStar_TypeChecker_Util.close_guard_implicits
                                              env1 tps3 guard
                                             in
                                          let t_tc =
                                            let uu____62459 =
                                              let uu____62468 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____62485 =
                                                let uu____62494 =
                                                  let uu____62507 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____62507
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____62494
                                                 in
                                              FStar_List.append uu____62468
                                                uu____62485
                                               in
                                            let uu____62530 =
                                              let uu____62533 =
                                                let uu____62534 =
                                                  let uu____62539 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____62539
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____62534
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____62533
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____62459 uu____62530
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____62556 =
                                            let uu____62561 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____62562 =
                                              let uu____62563 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____62563 k4
                                               in
                                            (uu____62561, uu____62562)  in
                                          match uu____62556 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____62583 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____62583,
                                                (let uu___646_62589 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_62589.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_62589.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_62589.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_62589.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____62594 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____62658 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____62658 with
             | (usubst,_uvs1) ->
                 let uu____62681 =
                   let uu____62686 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____62687 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____62686, uu____62687)  in
                 (match uu____62681 with
                  | (env1,t1) ->
                      let uu____62694 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____62733  ->
                               match uu____62733 with
                               | (se1,u_tc) ->
                                   let uu____62748 =
                                     let uu____62750 =
                                       let uu____62751 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____62751  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____62750
                                      in
                                   if uu____62748
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____62771,uu____62772,tps,uu____62774,uu____62775,uu____62776)
                                          ->
                                          let tps1 =
                                            let uu____62786 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____62786
                                              (FStar_List.map
                                                 (fun uu____62826  ->
                                                    match uu____62826 with
                                                    | (x,uu____62840) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____62848 =
                                            let uu____62855 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____62855, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____62848
                                      | uu____62862 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____62905 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____62905
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____62694 with
                       | (env2,tps,u_tc) ->
                           let uu____62937 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____62953 =
                               let uu____62954 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____62954.FStar_Syntax_Syntax.n  in
                             match uu____62953 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____62993 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____62993 with
                                  | (uu____63034,bs') ->
                                      let t3 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (bs', res))
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let subst1 =
                                        FStar_All.pipe_right tps
                                          (FStar_List.mapi
                                             (fun i  ->
                                                fun uu____63105  ->
                                                  match uu____63105 with
                                                  | (x,uu____63114) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____63121 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____63121)
                             | uu____63122 -> ([], t2)  in
                           (match uu____62937 with
                            | (arguments,result) ->
                                ((let uu____63166 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____63166
                                  then
                                    let uu____63169 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____63171 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____63174 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____63169 uu____63171 uu____63174
                                  else ());
                                 (let uu____63179 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____63179 with
                                  | (arguments1,env',us) ->
                                      let type_u_tc =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_type u_tc)
                                          FStar_Pervasives_Native.None
                                          result.FStar_Syntax_Syntax.pos
                                         in
                                      let env'1 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          env' type_u_tc
                                         in
                                      let uu____63197 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____63197 with
                                       | (result1,res_lcomp) ->
                                           let uu____63208 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____63208 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____63266 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____63266
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____63348  ->
                                                      fun uu____63349  ->
                                                        match (uu____63348,
                                                                uu____63349)
                                                        with
                                                        | ((bv,uu____63379),
                                                           (t2,uu____63381))
                                                            ->
                                                            let uu____63408 =
                                                              let uu____63409
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____63409.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____63408
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____63413 ->
                                                                 let uu____63414
                                                                   =
                                                                   let uu____63420
                                                                    =
                                                                    let uu____63422
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____63424
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____63422
                                                                    uu____63424
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____63420)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____63414
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____63429 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____63429
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____63431 =
                                                     let uu____63432 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____63432.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____63431 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____63435 -> ()
                                                   | uu____63436 ->
                                                       let uu____63437 =
                                                         let uu____63443 =
                                                           let uu____63445 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____63447 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____63445
                                                             uu____63447
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____63443)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____63437
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____63452 =
                                                       let uu____63453 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____63453.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____63452 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____63457;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____63458;_},tuvs)
                                                         when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         if
                                                           (FStar_List.length
                                                              _uvs1)
                                                             =
                                                             (FStar_List.length
                                                                tuvs)
                                                         then
                                                           FStar_List.fold_left2
                                                             (fun g  ->
                                                                fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____63472
                                                                    =
                                                                    let uu____63473
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____63474
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'1
                                                                    uu____63473
                                                                    uu____63474
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____63472)
                                                             FStar_TypeChecker_Env.trivial_guard
                                                             tuvs _uvs1
                                                         else
                                                           FStar_Errors.raise_error
                                                             (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                               "Length of annotated universes does not match inferred universes")
                                                             se.FStar_Syntax_Syntax.sigrng
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv when
                                                         FStar_Syntax_Syntax.fv_eq_lid
                                                           fv tc_lid
                                                         ->
                                                         FStar_TypeChecker_Env.trivial_guard
                                                     | uu____63480 ->
                                                         let uu____63481 =
                                                           let uu____63487 =
                                                             let uu____63489
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____63491
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____63489
                                                               uu____63491
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____63487)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____63481
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____63509  ->
                                                            fun u_x  ->
                                                              match uu____63509
                                                              with
                                                              | (x,uu____63518)
                                                                  ->
                                                                  let uu____63523
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____63523)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____63527 =
                                                       let uu____63536 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____63576 
                                                                 ->
                                                                 match uu____63576
                                                                 with
                                                                 | (x,uu____63590)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____63536
                                                         arguments1
                                                        in
                                                     let uu____63604 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____63527
                                                       uu____63604
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_63609 = se
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (c, _uvs1, t3,
                                                              tc_lid, ntps,
                                                              []));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___768_63609.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_63609.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_63609.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_63609.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____63613 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list
        ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs  in
          let g1 =
            let uu___776_63680 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_63680.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_63680.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_63680.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____63690 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____63690
           then
             let uu____63695 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____63695
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____63738  ->
                     match uu____63738 with
                     | (se,uu____63744) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____63745,uu____63746,tps,k,uu____63749,uu____63750)
                              ->
                              let uu____63759 =
                                let uu____63760 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____63760
                                 in
                              FStar_Syntax_Syntax.null_binder uu____63759
                          | uu____63765 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____63794,uu____63795,t,uu____63797,uu____63798,uu____63799)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____63806 -> failwith "Impossible"))
              in
           let t =
             let uu____63811 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____63811
              in
           (let uu____63821 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____63821
            then
              let uu____63826 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____63826
            else ());
           (let uu____63831 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____63831 with
            | (uvs,t1) ->
                ((let uu____63851 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____63851
                  then
                    let uu____63856 =
                      let uu____63858 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____63858
                        (FStar_String.concat ", ")
                       in
                    let uu____63875 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____63856 uu____63875
                  else ());
                 (let uu____63880 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____63880 with
                  | (uvs1,t2) ->
                      let uu____63895 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____63895 with
                       | (args,uu____63919) ->
                           let uu____63940 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____63940 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____64045  ->
                                       fun uu____64046  ->
                                         match (uu____64045, uu____64046)
                                         with
                                         | ((x,uu____64068),(se,uu____64070))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____64086,tps,uu____64088,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____64100 =
                                                    let uu____64105 =
                                                      let uu____64106 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____64106.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____64105 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____64135 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____64135
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____64213
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____64232 -> ([], ty)
                                                     in
                                                  (match uu____64100 with
                                                   | (tps1,t3) ->
                                                       let uu___853_64241 =
                                                         se  in
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
                                                           (uu___853_64241.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_64241.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_64241.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_64241.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____64246 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____64253 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _64257  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _64257))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_64276  ->
                                                match uu___585_64276 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____64282,uu____64283,uu____64284,uu____64285,uu____64286);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____64287;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____64288;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____64289;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____64290;_}
                                                    -> (tc, uvs_universes)
                                                | uu____64303 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____64327  ->
                                           fun d  ->
                                             match uu____64327 with
                                             | (t3,uu____64336) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____64342,uu____64343,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____64354 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____64354
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_64355 = d
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_datacon
                                                             (l, uvs1, ty,
                                                               tc, ntps,
                                                               mutuals));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___889_64355.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_64355.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_64355.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_64355.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____64359 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____64378 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____64378
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____64400 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____64400
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____64417 =
      let uu____64418 = FStar_Syntax_Subst.compress t  in
      uu____64418.FStar_Syntax_Syntax.n  in
    match uu____64417 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____64437 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____64443 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_ST.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid  ->
    fun arrghs  ->
      fun unfolded  ->
        fun env  ->
          let uu____64480 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____64529  ->
               match uu____64529 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____64573 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____64573  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____64480
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____64778 =
             let uu____64780 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____64780
              in
           debug_log env uu____64778);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype
              in
           (let uu____64785 =
              let uu____64787 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____64787
               in
            debug_log env uu____64785);
           (let uu____64792 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____64792) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____64805 =
                  let uu____64806 = FStar_Syntax_Subst.compress btype1  in
                  uu____64806.FStar_Syntax_Syntax.n  in
                match uu____64805 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____64836 = try_get_fv t  in
                    (match uu____64836 with
                     | (fv,us) ->
                         let uu____64844 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____64844
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____64860  ->
                                 match uu____64860 with
                                 | (t1,uu____64869) ->
                                     let uu____64874 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____64874) args)
                         else
                           (debug_log env
                              "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity";
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env "Checking strict positivity in Tm_arrow";
                     (let check_comp1 =
                        let c1 =
                          let uu____64909 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____64909
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____64913 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____64913
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           "Checking strict positivity , the arrow is impure, so return true";
                         true)
                      else
                        (debug_log env
                           "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type";
                         (FStar_List.for_all
                            (fun uu____64940  ->
                               match uu____64940 with
                               | (b,uu____64949) ->
                                   let uu____64954 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____64954) sbs)
                           &&
                           ((let uu____64960 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____64960 with
                             | (uu____64966,return_type) ->
                                 let uu____64968 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____64968)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____64969 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____64973 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____64978) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____64986) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____64993,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____65052  ->
                          match uu____65052 with
                          | (p,uu____65065,t) ->
                              let bs =
                                let uu____65084 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____65084
                                 in
                              let uu____65093 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____65093 with
                               | (bs1,t1) ->
                                   let uu____65101 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____65101)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____65103,uu____65104)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____65147 ->
                    ((let uu____65149 =
                        let uu____65151 =
                          let uu____65153 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____65155 =
                            let uu____65157 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____65157  in
                          Prims.op_Hat uu____65153 uu____65155  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____65151
                         in
                      debug_log env uu____65149);
                     false)))))

and (ty_nested_positive_in_inductive :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun ilid  ->
      fun us  ->
        fun args  ->
          fun unfolded  ->
            fun env  ->
              (let uu____65170 =
                 let uu____65172 =
                   let uu____65174 =
                     let uu____65176 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____65176  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____65174  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____65172
                  in
               debug_log env uu____65170);
              (let uu____65180 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____65180 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____65199 =
                       let uu____65201 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____65201
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____65199
                      then
                        ((let uu____65205 =
                            let uu____65207 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____65207
                             in
                          debug_log env uu____65205);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____65218 =
                        already_unfolded ilid args unfolded env  in
                      if uu____65218
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____65229 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____65229  in
                         (let uu____65235 =
                            let uu____65237 =
                              let uu____65239 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____65239
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____65237
                             in
                          debug_log env uu____65235);
                         (let uu____65244 =
                            let uu____65245 = FStar_ST.op_Bang unfolded  in
                            let uu____65271 =
                              let uu____65278 =
                                let uu____65283 =
                                  let uu____65284 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____65284  in
                                (ilid, uu____65283)  in
                              [uu____65278]  in
                            FStar_List.append uu____65245 uu____65271  in
                          FStar_ST.op_Colon_Equals unfolded uu____65244);
                         FStar_List.for_all
                           (fun d  ->
                              ty_nested_positive_in_dlid ty_lid d ilid us
                                args num_ibs unfolded env) idatas)))

and (ty_nested_positive_in_dlid :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            Prims.int ->
              unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
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
                    (Prims.op_Hat
                       "Checking nested positivity in data constructor "
                       (Prims.op_Hat dlid.FStar_Ident.str
                          (Prims.op_Hat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____65383 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____65383 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____65406 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Env.Iota;
                             FStar_TypeChecker_Env.Zeta;
                             FStar_TypeChecker_Env.AllowUnboundUniverses] env
                             dt
                            in
                         (let uu____65410 =
                            let uu____65412 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____65412
                             in
                          debug_log env uu____65410);
                         (let uu____65415 =
                            let uu____65416 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____65416.FStar_Syntax_Syntax.n  in
                          match uu____65415 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____65444 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____65444 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____65508 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____65508 dbs1
                                       in
                                    let c1 =
                                      let uu____65512 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____65512 c
                                       in
                                    let uu____65515 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____65515 with
                                     | (args1,uu____65550) ->
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
                                             args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst1 dbs2
                                            in
                                         let c2 =
                                           let uu____65642 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____65642 c1
                                            in
                                         ((let uu____65652 =
                                             let uu____65654 =
                                               let uu____65656 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____65659 =
                                                 let uu____65661 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____65661
                                                  in
                                               Prims.op_Hat uu____65656
                                                 uu____65659
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____65654
                                              in
                                           debug_log env uu____65652);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____65675 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____65678 =
                                  let uu____65679 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____65679.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____65678
                                  ilid num_ibs unfolded env))))))

and (ty_nested_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' ->
      FStar_Ident.lident ->
        Prims.int ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
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
                   (let uu____65718 = try_get_fv t1  in
                    match uu____65718 with
                    | (fv,uu____65725) ->
                        let uu____65726 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____65726
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____65758 =
                      let uu____65760 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____65760
                       in
                    debug_log env uu____65758);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____65765 =
                      FStar_List.fold_left
                        (fun uu____65786  ->
                           fun b  ->
                             match uu____65786 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____65817 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____65821 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____65817, uu____65821))) (true, env)
                        sbs1
                       in
                    match uu____65765 with | (b,uu____65839) -> b))
              | uu____65842 ->
                  failwith "Nested positive check, unhandled case"

let (ty_positive_in_datacon :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.universes ->
          unfolded_memo_t -> FStar_TypeChecker_Env.env -> Prims.bool)
  =
  fun ty_lid  ->
    fun dlid  ->
      fun ty_bs  ->
        fun us  ->
          fun unfolded  ->
            fun env  ->
              let uu____65878 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____65878 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____65901 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____65904 =
                      let uu____65906 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____65906
                       in
                    debug_log env uu____65904);
                   (let uu____65909 =
                      let uu____65910 = FStar_Syntax_Subst.compress dt  in
                      uu____65910.FStar_Syntax_Syntax.n  in
                    match uu____65909 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____65914 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____65919) ->
                        let dbs1 =
                          let uu____65949 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____65949  in
                        let dbs2 =
                          let uu____65999 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____65999 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____66004 =
                            let uu____66006 =
                              let uu____66008 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____66008 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____66006
                             in
                          debug_log env uu____66004);
                         (let uu____66018 =
                            FStar_List.fold_left
                              (fun uu____66039  ->
                                 fun b  ->
                                   match uu____66039 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____66070 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____66074 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____66070, uu____66074)))
                              (true, env) dbs3
                             in
                          match uu____66018 with | (b,uu____66092) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____66095,uu____66096) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____66132 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____66155 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____66171,uu____66172,uu____66173) -> (lid, us, bs)
        | uu____66182 -> failwith "Impossible!"  in
      match uu____66155 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____66194 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____66194 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____66218 =
                 let uu____66221 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____66221  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____66235 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____66235
                      unfolded_inductives env2) uu____66218)
  
let (check_exn_positivity :
  FStar_Ident.lid -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun data_ctor_lid  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] []
        unfolded_inductives env
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____66270,uu____66271,t,uu____66273,uu____66274,uu____66275) -> t
    | uu____66282 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____66299 =
         let uu____66301 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____66301 haseq_suffix  in
       uu____66299 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____66311 =
      let uu____66314 =
        let uu____66317 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____66317]  in
      FStar_List.append lid.FStar_Ident.ns uu____66314  in
    FStar_Ident.lid_of_ids uu____66311
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident * FStar_Syntax_Syntax.term *
            FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders *
            FStar_Syntax_Syntax.term))
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____66363 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____66377,bs,t,uu____66380,uu____66381) ->
                (lid, bs, t)
            | uu____66390 -> failwith "Impossible!"  in
          match uu____66363 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____66413 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____66413 t  in
              let uu____66422 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____66422 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____66440 =
                       let uu____66441 = FStar_Syntax_Subst.compress t2  in
                       uu____66441.FStar_Syntax_Syntax.n  in
                     match uu____66440 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____66445) -> ibs
                     | uu____66466 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____66475 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____66476 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____66475 uu____66476
                      in
                   let ind1 =
                     let uu____66482 =
                       let uu____66487 =
                         FStar_List.map
                           (fun uu____66504  ->
                              match uu____66504 with
                              | (bv,aq) ->
                                  let uu____66523 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____66523, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____66487  in
                     uu____66482 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____66529 =
                       let uu____66534 =
                         FStar_List.map
                           (fun uu____66551  ->
                              match uu____66551 with
                              | (bv,aq) ->
                                  let uu____66570 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____66570, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____66534  in
                     uu____66529 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____66576 =
                       let uu____66581 =
                         let uu____66582 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____66582]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____66581
                        in
                     uu____66576 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____66631 =
                            let uu____66632 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____66632  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____66631) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____66645 =
                              let uu____66648 =
                                let uu____66653 =
                                  let uu____66654 =
                                    let uu____66663 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____66663
                                     in
                                  [uu____66654]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____66653
                                 in
                              uu____66648 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____66645)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_66686 = fml  in
                     let uu____66687 =
                       let uu____66688 =
                         let uu____66695 =
                           let uu____66696 =
                             let uu____66709 =
                               let uu____66720 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____66720]  in
                             [uu____66709]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____66696  in
                         (fml, uu____66695)  in
                       FStar_Syntax_Syntax.Tm_meta uu____66688  in
                     {
                       FStar_Syntax_Syntax.n = uu____66687;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_66686.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_66686.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66773 =
                              let uu____66778 =
                                let uu____66779 =
                                  let uu____66788 =
                                    let uu____66789 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66789
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66788  in
                                [uu____66779]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66778
                               in
                            uu____66773 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66842 =
                              let uu____66847 =
                                let uu____66848 =
                                  let uu____66857 =
                                    let uu____66858 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66858
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66857  in
                                [uu____66848]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66847
                               in
                            uu____66842 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  
let (optimized_haseq_soundness_for_data :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun ty_lid  ->
    fun data  ->
      fun usubst  ->
        fun bs  ->
          let dt = datacon_typ data  in
          let dt1 = FStar_Syntax_Subst.subst usubst dt  in
          let uu____66933 =
            let uu____66934 = FStar_Syntax_Subst.compress dt1  in
            uu____66934.FStar_Syntax_Syntax.n  in
          match uu____66933 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____66938) ->
              let dbs1 =
                let uu____66968 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____66968  in
              let dbs2 =
                let uu____67018 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____67018 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____67033 =
                           let uu____67038 =
                             let uu____67039 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____67039]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____67038
                            in
                         uu____67033 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____67070 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____67070 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____67078 =
                       let uu____67083 =
                         let uu____67084 =
                           let uu____67093 =
                             let uu____67094 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____67094
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____67093  in
                         [uu____67084]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____67083
                        in
                     uu____67078 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____67141 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list *
              FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term'
              FStar_Syntax_Syntax.syntax))
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____67232,uu____67233,uu____67234,uu____67235,uu____67236)
                  -> lid
              | uu____67245 -> failwith "Impossible!"  in
            let uu____67247 = acc  in
            match uu____67247 with
            | (uu____67284,en,uu____67286,uu____67287) ->
                let uu____67308 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____67308 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____67345 = acc  in
                     (match uu____67345 with
                      | (l_axioms,env,guard',cond') ->
                          let env1 =
                            FStar_TypeChecker_Env.push_binders env bs  in
                          let env2 =
                            FStar_TypeChecker_Env.push_binders env1 ibs  in
                          let t_datas =
                            FStar_List.filter
                              (fun s  ->
                                 match s.FStar_Syntax_Syntax.sigel with
                                 | FStar_Syntax_Syntax.Sig_datacon
                                     (uu____67420,uu____67421,uu____67422,t_lid,uu____67424,uu____67425)
                                     -> t_lid = lid
                                 | uu____67432 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____67447 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____67447)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____67450 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____67453 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____67450, uu____67453)))
  
let (optimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let uu____67511 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____67521,us,uu____67523,t,uu____67525,uu____67526) ->
                (us, t)
            | uu____67535 -> failwith "Impossible!"  in
          match uu____67511 with
          | (us,t) ->
              let uu____67545 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____67545 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____67571 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____67571 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____67649 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____67649 with
                           | (uu____67664,t1) ->
                               let uu____67686 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____67686
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____67691 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____67691 with
                          | (phi1,uu____67699) ->
                              ((let uu____67701 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____67701
                                then
                                  let uu____67704 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____67704
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____67722  ->
                                         match uu____67722 with
                                         | (lid,fml) ->
                                             let fml1 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 us1 fml
                                                in
                                             FStar_List.append l
                                               [{
                                                  FStar_Syntax_Syntax.sigel =
                                                    (FStar_Syntax_Syntax.Sig_assume
                                                       (lid, us1, fml1));
                                                  FStar_Syntax_Syntax.sigrng
                                                    = FStar_Range.dummyRange;
                                                  FStar_Syntax_Syntax.sigquals
                                                    = [];
                                                  FStar_Syntax_Syntax.sigmeta
                                                    =
                                                    FStar_Syntax_Syntax.default_sigmeta;
                                                  FStar_Syntax_Syntax.sigattrs
                                                    = []
                                                }]) [] axioms
                                   in
                                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                                  "haseq";
                                ses))))))
  
let (unoptimized_haseq_data :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lident Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun usubst  ->
    fun bs  ->
      fun haseq_ind  ->
        fun mutuals  ->
          fun acc  ->
            fun data  ->
              let rec is_mutual t =
                let uu____67794 =
                  let uu____67795 = FStar_Syntax_Subst.compress t  in
                  uu____67795.FStar_Syntax_Syntax.n  in
                match uu____67794 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____67803) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____67840 = is_mutual t'  in
                    if uu____67840
                    then true
                    else
                      (let uu____67847 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____67847)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____67867) ->
                    is_mutual t'
                | uu____67872 -> false
              
              and exists_mutual uu___586_67874 =
                match uu___586_67874 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____67895 =
                let uu____67896 = FStar_Syntax_Subst.compress dt1  in
                uu____67896.FStar_Syntax_Syntax.n  in
              match uu____67895 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____67902) ->
                  let dbs1 =
                    let uu____67932 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____67932  in
                  let dbs2 =
                    let uu____67982 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____67982 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____68002 =
                               let uu____68007 =
                                 let uu____68008 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____68008]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____68007
                                in
                             uu____68002 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____68038 = is_mutual sort  in
                             if uu____68038
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
                           let uu____68051 =
                             let uu____68056 =
                               let uu____68057 =
                                 let uu____68066 =
                                   let uu____68067 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____68067 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____68066  in
                               [uu____68057]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____68056
                              in
                           uu____68051 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____68114 -> acc
  
let (unoptimized_haseq_ty :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Ident.lident Prims.list ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.sigelt ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun all_datas_in_the_bundle  ->
    fun mutuals  ->
      fun usubst  ->
        fun us  ->
          fun acc  ->
            fun ty  ->
              let uu____68164 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____68186,bs,t,uu____68189,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____68201 -> failwith "Impossible!"  in
              match uu____68164 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____68225 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____68225 t  in
                  let uu____68234 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____68234 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____68244 =
                           let uu____68245 = FStar_Syntax_Subst.compress t2
                              in
                           uu____68245.FStar_Syntax_Syntax.n  in
                         match uu____68244 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____68249) ->
                             ibs
                         | uu____68270 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____68279 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____68280 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____68279
                           uu____68280
                          in
                       let ind1 =
                         let uu____68286 =
                           let uu____68291 =
                             FStar_List.map
                               (fun uu____68308  ->
                                  match uu____68308 with
                                  | (bv,aq) ->
                                      let uu____68327 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____68327, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____68291  in
                         uu____68286 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____68333 =
                           let uu____68338 =
                             FStar_List.map
                               (fun uu____68355  ->
                                  match uu____68355 with
                                  | (bv,aq) ->
                                      let uu____68374 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____68374, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____68338  in
                         uu____68333 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____68380 =
                           let uu____68385 =
                             let uu____68386 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____68386]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____68385
                            in
                         uu____68380 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____68423,uu____68424,uu____68425,t_lid,uu____68427,uu____68428)
                                  -> t_lid = lid
                              | uu____68435 -> failwith "Impossible")
                           all_datas_in_the_bundle
                          in
                       let data_cond =
                         FStar_List.fold_left
                           (unoptimized_haseq_data usubst bs2 haseq_ind
                              mutuals) FStar_Syntax_Util.t_true t_datas
                          in
                       let fml = FStar_Syntax_Util.mk_imp data_cond haseq_ind
                          in
                       let fml1 =
                         let uu___1460_68447 = fml  in
                         let uu____68448 =
                           let uu____68449 =
                             let uu____68456 =
                               let uu____68457 =
                                 let uu____68470 =
                                   let uu____68481 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____68481]  in
                                 [uu____68470]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____68457
                                in
                             (fml, uu____68456)  in
                           FStar_Syntax_Syntax.Tm_meta uu____68449  in
                         {
                           FStar_Syntax_Syntax.n = uu____68448;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_68447.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_68447.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____68534 =
                                  let uu____68539 =
                                    let uu____68540 =
                                      let uu____68549 =
                                        let uu____68550 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____68550
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____68549
                                       in
                                    [uu____68540]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____68539
                                   in
                                uu____68534 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____68603 =
                                  let uu____68608 =
                                    let uu____68609 =
                                      let uu____68618 =
                                        let uu____68619 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____68619
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____68618
                                       in
                                    [uu____68609]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____68608
                                   in
                                uu____68603 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) bs2 fml2
                          in
                       FStar_Syntax_Util.mk_conj acc fml3)
  
let (unoptimized_haseq_scheme :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_TypeChecker_Env.env_t -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sig_bndle  ->
    fun tcs  ->
      fun datas  ->
        fun env0  ->
          let mutuals =
            FStar_List.map
              (fun ty  ->
                 match ty.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____68711,uu____68712,uu____68713,uu____68714,uu____68715)
                     -> lid
                 | uu____68724 -> failwith "Impossible!") tcs
             in
          let uu____68726 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____68738,uu____68739,uu____68740,uu____68741) ->
                (lid, us)
            | uu____68750 -> failwith "Impossible!"  in
          match uu____68726 with
          | (lid,us) ->
              let uu____68760 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____68760 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____68787 =
                       let uu____68788 =
                         let uu____68795 = get_haseq_axiom_lid lid  in
                         (uu____68795, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____68788  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____68787;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = []
                     }  in
                   [se])
  
let (check_inductive_well_typedness :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list
            * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____68849 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_68874  ->
                    match uu___587_68874 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____68876;
                        FStar_Syntax_Syntax.sigrng = uu____68877;
                        FStar_Syntax_Syntax.sigquals = uu____68878;
                        FStar_Syntax_Syntax.sigmeta = uu____68879;
                        FStar_Syntax_Syntax.sigattrs = uu____68880;_} -> true
                    | uu____68902 -> false))
             in
          match uu____68849 with
          | (tys,datas) ->
              ((let uu____68925 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_68936  ->
                          match uu___588_68936 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____68938;
                              FStar_Syntax_Syntax.sigrng = uu____68939;
                              FStar_Syntax_Syntax.sigquals = uu____68940;
                              FStar_Syntax_Syntax.sigmeta = uu____68941;
                              FStar_Syntax_Syntax.sigattrs = uu____68942;_}
                              -> false
                          | uu____68963 -> true))
                   in
                if uu____68925
                then
                  let uu____68966 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____68966
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____68981 =
                       let uu____68982 = FStar_List.hd tys  in
                       uu____68982.FStar_Syntax_Syntax.sigel  in
                     match uu____68981 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____68985,uvs,uu____68987,uu____68988,uu____68989,uu____68990)
                         -> uvs
                     | uu____68999 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____69004 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____69034 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____69034 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____69072,bs,t,l1,l2) ->
                                      let uu____69085 =
                                        let uu____69102 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____69103 =
                                          let uu____69104 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____69104 t
                                           in
                                        (lid, univs2, uu____69102,
                                          uu____69103, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____69085
                                  | uu____69117 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_69119 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_69119.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_69119.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_69119.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_69119.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____69129,t,lid_t,x,l) ->
                                      let uu____69140 =
                                        let uu____69156 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____69156, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____69140
                                  | uu____69160 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_69162 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_69162.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_69162.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_69162.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_69162.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____69163 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____69163, tys1, datas1))
                   in
                match uu____69004 with
                | (env1,tys1,datas1) ->
                    let uu____69189 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____69228  ->
                             match uu____69228 with
                             | (env2,all_tcs,g) ->
                                 let uu____69268 = tc_tycon env2 tc  in
                                 (match uu____69268 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____69295 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____69295
                                        then
                                          let uu____69298 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____69298
                                        else ());
                                       (let uu____69303 =
                                          let uu____69304 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____69304
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____69303))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____69189 with
                     | (env2,tcs,g) ->
                         let uu____69350 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____69372  ->
                                  match uu____69372 with
                                  | (datas2,g1) ->
                                      let uu____69391 =
                                        let uu____69396 = tc_data env2 tcs
                                           in
                                        uu____69396 se  in
                                      (match uu____69391 with
                                       | (data,g') ->
                                           let uu____69413 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____69413)))
                             datas1 ([], g)
                            in
                         (match uu____69350 with
                          | (datas2,g1) ->
                              let uu____69434 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____69456 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____69456, datas2))
                                 in
                              (match uu____69434 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____69488 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____69489 =
                                       FStar_List.collect
                                         (fun s  ->
                                            s.FStar_Syntax_Syntax.sigattrs)
                                         ses
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_bundle
                                            ((FStar_List.append tcs1 datas3),
                                              lids));
                                       FStar_Syntax_Syntax.sigrng =
                                         uu____69488;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____69489
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____69515,uu____69516)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____69536 =
                                                    let uu____69542 =
                                                      let uu____69544 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____69546 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____69544
                                                        uu____69546
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____69542)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____69536
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____69550 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____69550 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____69566)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____69597 ->
                                                             let uu____69598
                                                               =
                                                               let uu____69605
                                                                 =
                                                                 let uu____69606
                                                                   =
                                                                   let uu____69621
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____69621)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____69606
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____69605
                                                                in
                                                             uu____69598
                                                               FStar_Pervasives_Native.None
                                                               se.FStar_Syntax_Syntax.sigrng
                                                          in
                                                       (univs2, body)  in
                                                     if
                                                       (FStar_List.length
                                                          univs2)
                                                         =
                                                         (FStar_List.length
                                                            (FStar_Pervasives_Native.fst
                                                               expected_typ1))
                                                     then
                                                       let uu____69643 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____69643
                                                        with
                                                        | (uu____69648,inferred)
                                                            ->
                                                            let uu____69650 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____69650
                                                             with
                                                             | (uu____69655,expected)
                                                                 ->
                                                                 let uu____69657
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____69657
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____69664 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))
  
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"] 
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____69775 =
                            let uu____69782 =
                              let uu____69783 =
                                let uu____69790 =
                                  let uu____69793 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____69793
                                   in
                                (uu____69790, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____69783  in
                            FStar_Syntax_Syntax.mk uu____69782  in
                          uu____69775 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____69827  ->
                                  match uu____69827 with
                                  | (x,imp) ->
                                      let uu____69846 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____69846, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____69850 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____69850  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               let uu____69873 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____69873
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____69875 =
                               let uu____69878 =
                                 let uu____69881 =
                                   let uu____69886 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____69887 =
                                     let uu____69888 =
                                       let uu____69897 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____69897
                                        in
                                     [uu____69888]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____69886
                                     uu____69887
                                    in
                                 uu____69881 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____69878  in
                             FStar_Syntax_Util.refine x uu____69875  in
                           let uu____69922 =
                             let uu___1671_69923 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_69923.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_69923.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____69922)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____69940 =
                          FStar_List.map
                            (fun uu____69964  ->
                               match uu____69964 with
                               | (x,uu____69978) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____69940 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____70037  ->
                                match uu____70037 with
                                | (x,uu____70051) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____70062 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____70062)
                          &&
                          (FStar_List.existsb
                             (fun s  ->
                                s = (tc.FStar_Ident.ident).FStar_Ident.idText)
                             early_prims_inductives)
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             early_prims_inductive ||
                               (let uu____70083 =
                                  let uu____70085 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____70085.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____70083)
                              in
                           let quals =
                             let uu____70089 =
                               FStar_List.filter
                                 (fun uu___589_70093  ->
                                    match uu___589_70093 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____70098 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____70089
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____70136 =
                                 let uu____70137 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____70137  in
                               FStar_Syntax_Syntax.mk_Total uu____70136  in
                             let uu____70138 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____70138
                              in
                           let decl =
                             let uu____70142 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____70142;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____70144 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____70144
                            then
                              let uu____70148 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____70148
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Util.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____70209  ->
                                               match uu____70209 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____70234 =
                                                       let uu____70237 =
                                                         let uu____70238 =
                                                           let uu____70245 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____70245,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____70238
                                                          in
                                                       pos uu____70237  in
                                                     (uu____70234, b)
                                                   else
                                                     (let uu____70253 =
                                                        let uu____70256 =
                                                          let uu____70257 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____70257
                                                           in
                                                        pos uu____70256  in
                                                      (uu____70253, b))))
                                      in
                                   let pat_true =
                                     let uu____70276 =
                                       let uu____70279 =
                                         let uu____70280 =
                                           let uu____70294 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____70294, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____70280
                                          in
                                       pos uu____70279  in
                                     (uu____70276,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____70329 =
                                       let uu____70332 =
                                         let uu____70333 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____70333
                                          in
                                       pos uu____70332  in
                                     (uu____70329,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____70347 =
                                     let uu____70354 =
                                       let uu____70355 =
                                         let uu____70378 =
                                           let uu____70395 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____70410 =
                                             let uu____70427 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____70427]  in
                                           uu____70395 :: uu____70410  in
                                         (arg_exp, uu____70378)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70355
                                        in
                                     FStar_Syntax_Syntax.mk uu____70354  in
                                   uu____70347 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____70503 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____70503
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                       (Prims.parse_int "1"))
                                else
                                  FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")
                                 in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____70525 =
                                  let uu____70530 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____70530  in
                                let uu____70531 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____70525
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____70531 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____70537 =
                                  let uu____70538 =
                                    let uu____70545 =
                                      let uu____70548 =
                                        let uu____70549 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____70549
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____70548]  in
                                    ((false, [lb]), uu____70545)  in
                                  FStar_Syntax_Syntax.Sig_let uu____70538  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____70537;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____70563 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____70563
                               then
                                 let uu____70567 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____70567
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____70640  ->
                                  match uu____70640 with
                                  | (a,uu____70649) ->
                                      let uu____70654 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____70654 with
                                       | (field_name,uu____70660) ->
                                           let field_proj_tm =
                                             let uu____70662 =
                                               let uu____70663 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____70663
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____70662 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____70689 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____70731  ->
                                    match uu____70731 with
                                    | (x,uu____70742) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____70748 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____70748 with
                                         | (field_name,uu____70756) ->
                                             let t =
                                               let uu____70760 =
                                                 let uu____70761 =
                                                   let uu____70764 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____70764
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____70761
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____70760
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____70770 =
                                                    let uu____70772 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____70772.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____70770)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____70791 =
                                                   FStar_List.filter
                                                     (fun uu___590_70795  ->
                                                        match uu___590_70795
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____70798 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____70791
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_70813  ->
                                                         match uu___591_70813
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____70819 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
                                             let decl =
                                               let uu____70830 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____70830;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____70832 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____70832
                                               then
                                                 let uu____70836 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____70836
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____70890 
                                                             ->
                                                             match uu____70890
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____70916
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____70916,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____70932
                                                                    =
                                                                    let uu____70935
                                                                    =
                                                                    let uu____70936
                                                                    =
                                                                    let uu____70943
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____70943,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____70936
                                                                     in
                                                                    pos
                                                                    uu____70935
                                                                     in
                                                                    (uu____70932,
                                                                    b))
                                                                   else
                                                                    (let uu____70951
                                                                    =
                                                                    let uu____70954
                                                                    =
                                                                    let uu____70955
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____70955
                                                                     in
                                                                    pos
                                                                    uu____70954
                                                                     in
                                                                    (uu____70951,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____70974 =
                                                     let uu____70977 =
                                                       let uu____70978 =
                                                         let uu____70992 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____70992,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____70978
                                                        in
                                                     pos uu____70977  in
                                                   let uu____71002 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____70974,
                                                     FStar_Pervasives_Native.None,
                                                     uu____71002)
                                                    in
                                                 let body =
                                                   let uu____71018 =
                                                     let uu____71025 =
                                                       let uu____71026 =
                                                         let uu____71049 =
                                                           let uu____71066 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____71066]  in
                                                         (arg_exp,
                                                           uu____71049)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____71026
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____71025
                                                      in
                                                   uu____71018
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____71131 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____71131
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       (FStar_Syntax_Syntax.Delta_equational_at_level
                                                          (Prims.parse_int "1"))
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational_at_level
                                                       (Prims.parse_int "1")
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____71150 =
                                                     let uu____71155 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____71155
                                                      in
                                                   let uu____71156 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____71150;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____71156;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____71162 =
                                                     let uu____71163 =
                                                       let uu____71170 =
                                                         let uu____71173 =
                                                           let uu____71174 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____71174
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____71173]  in
                                                       ((false, [lb]),
                                                         uu____71170)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____71163
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____71162;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____71188 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____71188
                                                  then
                                                    let uu____71192 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____71192
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____70689 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____71246) when
              let uu____71253 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____71253 ->
              let uu____71255 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____71255 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____71277 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____71277 with
                    | (formals,uu____71295) ->
                        let uu____71316 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____71351 =
                                   let uu____71353 =
                                     let uu____71354 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____71354  in
                                   FStar_Ident.lid_equals typ_lid uu____71353
                                    in
                                 if uu____71351
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____71376,uvs',tps,typ0,uu____71380,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____71400 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____71449 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____71449
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____71316 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____71487 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____71487 with
                              | (indices,uu____71505) ->
                                  let refine_domain =
                                    let uu____71528 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_71535  ->
                                              match uu___592_71535 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____71537 -> true
                                              | uu____71547 -> false))
                                       in
                                    if uu____71528
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_71562 =
                                      match uu___593_71562 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____71565,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____71577 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____71578 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____71578 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract iquals)
                                        &&
                                        (Prims.op_Negation
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Private
                                              iquals))
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____71591 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____71591 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____71674  ->
                                               fun uu____71675  ->
                                                 match (uu____71674,
                                                         uu____71675)
                                                 with
                                                 | ((x,uu____71701),(x',uu____71703))
                                                     ->
                                                     let uu____71724 =
                                                       let uu____71731 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____71731)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____71724) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____71736 -> []
  