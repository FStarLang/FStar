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
          let uu____66188 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____66188 with
           | (usubst,uvs1) ->
               let uu____66215 =
                 let uu____66222 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____66223 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____66224 =
                   let uu____66225 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____66225 k  in
                 (uu____66222, uu____66223, uu____66224)  in
               (match uu____66215 with
                | (env1,tps1,k1) ->
                    let uu____66245 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____66245 with
                     | (tps2,k2) ->
                         let uu____66260 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____66260 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____66281 =
                                let uu____66300 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____66300 with
                                | (k3,uu____66326,g) ->
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
                                    let uu____66329 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____66344 =
                                      let uu____66345 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____66345
                                       in
                                    (uu____66329, uu____66344)
                                 in
                              (match uu____66281 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____66408 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____66408
                                      in
                                   let uu____66411 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____66411 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____66429 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____66429))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____66436 =
                                              let uu____66442 =
                                                let uu____66444 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____66446 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____66444 uu____66446
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____66442)
                                               in
                                            FStar_Errors.raise_error
                                              uu____66436
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
                                            let uu____66459 =
                                              let uu____66468 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____66485 =
                                                let uu____66494 =
                                                  let uu____66507 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____66507
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____66494
                                                 in
                                              FStar_List.append uu____66468
                                                uu____66485
                                               in
                                            let uu____66530 =
                                              let uu____66533 =
                                                let uu____66534 =
                                                  let uu____66539 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____66539
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____66534
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____66533
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____66459 uu____66530
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____66556 =
                                            let uu____66561 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____66562 =
                                              let uu____66563 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____66563 k4
                                               in
                                            (uu____66561, uu____66562)  in
                                          match uu____66556 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____66583 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____66583,
                                                (let uu___646_66589 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_66589.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_66589.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_66589.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_66589.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____66594 -> failwith "impossible"
  
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
            let uu____66658 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____66658 with
             | (usubst,_uvs1) ->
                 let uu____66681 =
                   let uu____66686 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____66687 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____66686, uu____66687)  in
                 (match uu____66681 with
                  | (env1,t1) ->
                      let uu____66694 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____66733  ->
                               match uu____66733 with
                               | (se1,u_tc) ->
                                   let uu____66748 =
                                     let uu____66750 =
                                       let uu____66751 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____66751  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____66750
                                      in
                                   if uu____66748
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____66771,uu____66772,tps,uu____66774,uu____66775,uu____66776)
                                          ->
                                          let tps1 =
                                            let uu____66786 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____66786
                                              (FStar_List.map
                                                 (fun uu____66826  ->
                                                    match uu____66826 with
                                                    | (x,uu____66840) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____66848 =
                                            let uu____66855 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____66855, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____66848
                                      | uu____66862 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____66905 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____66905
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____66694 with
                       | (env2,tps,u_tc) ->
                           let uu____66937 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____66953 =
                               let uu____66954 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____66954.FStar_Syntax_Syntax.n  in
                             match uu____66953 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____66993 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____66993 with
                                  | (uu____67034,bs') ->
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
                                                fun uu____67105  ->
                                                  match uu____67105 with
                                                  | (x,uu____67114) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____67121 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____67121)
                             | uu____67122 -> ([], t2)  in
                           (match uu____66937 with
                            | (arguments,result) ->
                                ((let uu____67166 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____67166
                                  then
                                    let uu____67169 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____67171 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____67174 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____67169 uu____67171 uu____67174
                                  else ());
                                 (let uu____67179 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____67179 with
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
                                      let uu____67197 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____67197 with
                                       | (result1,res_lcomp) ->
                                           let uu____67208 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____67208 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____67266 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____67266
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____67348  ->
                                                      fun uu____67349  ->
                                                        match (uu____67348,
                                                                uu____67349)
                                                        with
                                                        | ((bv,uu____67379),
                                                           (t2,uu____67381))
                                                            ->
                                                            let uu____67408 =
                                                              let uu____67409
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____67409.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____67408
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____67413 ->
                                                                 let uu____67414
                                                                   =
                                                                   let uu____67420
                                                                    =
                                                                    let uu____67422
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____67424
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____67422
                                                                    uu____67424
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____67420)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____67414
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____67429 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____67429
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____67431 =
                                                     let uu____67432 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____67432.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____67431 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____67435 -> ()
                                                   | uu____67436 ->
                                                       let uu____67437 =
                                                         let uu____67443 =
                                                           let uu____67445 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____67447 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____67445
                                                             uu____67447
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____67443)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____67437
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____67452 =
                                                       let uu____67453 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____67453.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____67452 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____67457;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____67458;_},tuvs)
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
                                                                    let uu____67472
                                                                    =
                                                                    let uu____67473
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____67474
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
                                                                    uu____67473
                                                                    uu____67474
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67472)
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
                                                     | uu____67480 ->
                                                         let uu____67481 =
                                                           let uu____67487 =
                                                             let uu____67489
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____67491
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____67489
                                                               uu____67491
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____67487)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____67481
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____67509  ->
                                                            fun u_x  ->
                                                              match uu____67509
                                                              with
                                                              | (x,uu____67518)
                                                                  ->
                                                                  let uu____67523
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67523)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____67527 =
                                                       let uu____67536 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____67576 
                                                                 ->
                                                                 match uu____67576
                                                                 with
                                                                 | (x,uu____67590)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____67536
                                                         arguments1
                                                        in
                                                     let uu____67604 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____67527
                                                       uu____67604
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_67609 = se
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
                                                         (uu___768_67609.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_67609.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_67609.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_67609.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____67613 -> failwith "impossible"
  
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
            let uu___776_67680 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_67680.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_67680.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_67680.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____67690 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____67690
           then
             let uu____67695 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____67695
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____67738  ->
                     match uu____67738 with
                     | (se,uu____67744) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____67745,uu____67746,tps,k,uu____67749,uu____67750)
                              ->
                              let uu____67759 =
                                let uu____67760 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____67760
                                 in
                              FStar_Syntax_Syntax.null_binder uu____67759
                          | uu____67765 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____67794,uu____67795,t,uu____67797,uu____67798,uu____67799)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____67806 -> failwith "Impossible"))
              in
           let t =
             let uu____67811 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____67811
              in
           (let uu____67821 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____67821
            then
              let uu____67826 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____67826
            else ());
           (let uu____67831 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____67831 with
            | (uvs,t1) ->
                ((let uu____67851 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____67851
                  then
                    let uu____67856 =
                      let uu____67858 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____67858
                        (FStar_String.concat ", ")
                       in
                    let uu____67875 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____67856 uu____67875
                  else ());
                 (let uu____67880 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____67880 with
                  | (uvs1,t2) ->
                      let uu____67895 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____67895 with
                       | (args,uu____67919) ->
                           let uu____67940 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____67940 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____68045  ->
                                       fun uu____68046  ->
                                         match (uu____68045, uu____68046)
                                         with
                                         | ((x,uu____68068),(se,uu____68070))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____68086,tps,uu____68088,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____68100 =
                                                    let uu____68105 =
                                                      let uu____68106 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____68106.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____68105 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____68135 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____68135
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____68213
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____68232 -> ([], ty)
                                                     in
                                                  (match uu____68100 with
                                                   | (tps1,t3) ->
                                                       let uu___853_68241 =
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
                                                           (uu___853_68241.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_68241.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_68241.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_68241.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____68246 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____68253 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _68257  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _68257))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_68276  ->
                                                match uu___585_68276 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____68282,uu____68283,uu____68284,uu____68285,uu____68286);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____68287;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____68288;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____68289;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____68290;_}
                                                    -> (tc, uvs_universes)
                                                | uu____68303 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____68327  ->
                                           fun d  ->
                                             match uu____68327 with
                                             | (t3,uu____68336) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____68342,uu____68343,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____68354 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____68354
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_68355 = d
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
                                                          (uu___889_68355.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_68355.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_68355.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_68355.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____68359 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____68378 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____68378
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____68400 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____68400
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____68417 =
      let uu____68418 = FStar_Syntax_Subst.compress t  in
      uu____68418.FStar_Syntax_Syntax.n  in
    match uu____68417 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____68437 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____68443 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____68500 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____68569  ->
               match uu____68569 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____68613 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____68613  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____68500
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____68868 =
             let uu____68870 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____68870
              in
           debug_log env uu____68868);
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
           (let uu____68875 =
              let uu____68877 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____68877
               in
            debug_log env uu____68875);
           (let uu____68882 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____68882) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____68895 =
                  let uu____68896 = FStar_Syntax_Subst.compress btype1  in
                  uu____68896.FStar_Syntax_Syntax.n  in
                match uu____68895 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____68926 = try_get_fv t  in
                    (match uu____68926 with
                     | (fv,us) ->
                         let uu____68934 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____68934
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____68950  ->
                                 match uu____68950 with
                                 | (t1,uu____68959) ->
                                     let uu____68964 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____68964) args)
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
                          let uu____69019 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____69019
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____69023 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____69023
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
                            (fun uu____69050  ->
                               match uu____69050 with
                               | (b,uu____69059) ->
                                   let uu____69064 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____69064) sbs)
                           &&
                           ((let uu____69070 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____69070 with
                             | (uu____69076,return_type) ->
                                 let uu____69078 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____69078)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____69099 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____69103 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____69108) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____69136) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____69163,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____69222  ->
                          match uu____69222 with
                          | (p,uu____69235,t) ->
                              let bs =
                                let uu____69254 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____69254
                                 in
                              let uu____69263 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____69263 with
                               | (bs1,t1) ->
                                   let uu____69271 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____69271)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____69293,uu____69294)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____69357 ->
                    ((let uu____69359 =
                        let uu____69361 =
                          let uu____69363 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____69365 =
                            let uu____69367 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____69367  in
                          Prims.op_Hat uu____69363 uu____69365  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____69361
                         in
                      debug_log env uu____69359);
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
              (let uu____69390 =
                 let uu____69392 =
                   let uu____69394 =
                     let uu____69396 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____69396  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____69394  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____69392
                  in
               debug_log env uu____69390);
              (let uu____69400 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____69400 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____69419 =
                       let uu____69421 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____69421
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____69419
                      then
                        ((let uu____69425 =
                            let uu____69427 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____69427
                             in
                          debug_log env uu____69425);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____69438 =
                        already_unfolded ilid args unfolded env  in
                      if uu____69438
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____69469 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____69469  in
                         (let uu____69475 =
                            let uu____69477 =
                              let uu____69479 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____69479
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____69477
                             in
                          debug_log env uu____69475);
                         (let uu____69484 =
                            let uu____69485 = FStar_ST.op_Bang unfolded  in
                            let uu____69531 =
                              let uu____69538 =
                                let uu____69543 =
                                  let uu____69544 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____69544  in
                                (ilid, uu____69543)  in
                              [uu____69538]  in
                            FStar_List.append uu____69485 uu____69531  in
                          FStar_ST.op_Colon_Equals unfolded uu____69484);
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
                  (let uu____69693 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____69693 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____69716 ->
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
                         (let uu____69720 =
                            let uu____69722 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____69722
                             in
                          debug_log env uu____69720);
                         (let uu____69725 =
                            let uu____69726 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____69726.FStar_Syntax_Syntax.n  in
                          match uu____69725 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____69754 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____69754 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____69818 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____69818 dbs1
                                       in
                                    let c1 =
                                      let uu____69822 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____69822 c
                                       in
                                    let uu____69825 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____69825 with
                                     | (args1,uu____69860) ->
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
                                           let uu____69952 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____69952 c1
                                            in
                                         ((let uu____69962 =
                                             let uu____69964 =
                                               let uu____69966 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____69969 =
                                                 let uu____69971 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____69971
                                                  in
                                               Prims.op_Hat uu____69966
                                                 uu____69969
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____69964
                                              in
                                           debug_log env uu____69962);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____70005 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____70008 =
                                  let uu____70009 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____70009.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____70008
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
                   (let uu____70078 = try_get_fv t1  in
                    match uu____70078 with
                    | (fv,uu____70085) ->
                        let uu____70086 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____70086
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____70118 =
                      let uu____70120 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____70120
                       in
                    debug_log env uu____70118);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____70125 =
                      FStar_List.fold_left
                        (fun uu____70146  ->
                           fun b  ->
                             match uu____70146 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____70177 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____70201 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____70177, uu____70201))) (true, env)
                        sbs1
                       in
                    match uu____70125 with | (b,uu____70219) -> b))
              | uu____70222 ->
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
              let uu____70278 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____70278 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____70301 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____70304 =
                      let uu____70306 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____70306
                       in
                    debug_log env uu____70304);
                   (let uu____70309 =
                      let uu____70310 = FStar_Syntax_Subst.compress dt  in
                      uu____70310.FStar_Syntax_Syntax.n  in
                    match uu____70309 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____70314 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____70319) ->
                        let dbs1 =
                          let uu____70349 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____70349  in
                        let dbs2 =
                          let uu____70399 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____70399 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____70404 =
                            let uu____70406 =
                              let uu____70408 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____70408 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____70406
                             in
                          debug_log env uu____70404);
                         (let uu____70418 =
                            FStar_List.fold_left
                              (fun uu____70439  ->
                                 fun b  ->
                                   match uu____70439 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____70470 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____70494 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____70470, uu____70494)))
                              (true, env) dbs3
                             in
                          match uu____70418 with | (b,uu____70512) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____70515,uu____70516) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____70572 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____70595 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____70611,uu____70612,uu____70613) -> (lid, us, bs)
        | uu____70622 -> failwith "Impossible!"  in
      match uu____70595 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____70634 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____70634 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____70658 =
                 let uu____70661 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____70661  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____70675 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____70675
                      unfolded_inductives env2) uu____70658)
  
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
        (uu____70754,uu____70755,t,uu____70757,uu____70758,uu____70759) -> t
    | uu____70766 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____70793 =
         let uu____70795 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____70795 haseq_suffix  in
       uu____70793 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____70819 =
      let uu____70822 =
        let uu____70825 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____70825]  in
      FStar_List.append lid.FStar_Ident.ns uu____70822  in
    FStar_Ident.lid_of_ids uu____70819
  
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
          let uu____70871 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____70885,bs,t,uu____70888,uu____70889) ->
                (lid, bs, t)
            | uu____70898 -> failwith "Impossible!"  in
          match uu____70871 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____70921 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____70921 t  in
              let uu____70930 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____70930 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____70948 =
                       let uu____70949 = FStar_Syntax_Subst.compress t2  in
                       uu____70949.FStar_Syntax_Syntax.n  in
                     match uu____70948 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____70953) -> ibs
                     | uu____70974 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____70983 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____70984 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____70983 uu____70984
                      in
                   let ind1 =
                     let uu____70990 =
                       let uu____70995 =
                         FStar_List.map
                           (fun uu____71012  ->
                              match uu____71012 with
                              | (bv,aq) ->
                                  let uu____71031 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71031, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____70995  in
                     uu____70990 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____71039 =
                       let uu____71044 =
                         FStar_List.map
                           (fun uu____71061  ->
                              match uu____71061 with
                              | (bv,aq) ->
                                  let uu____71080 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71080, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____71044  in
                     uu____71039 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____71088 =
                       let uu____71093 =
                         let uu____71094 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____71094]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____71093
                        in
                     uu____71088 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____71145 =
                            let uu____71146 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____71146  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____71145) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____71159 =
                              let uu____71162 =
                                let uu____71167 =
                                  let uu____71168 =
                                    let uu____71177 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____71177
                                     in
                                  [uu____71168]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____71167
                                 in
                              uu____71162 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____71159)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_71202 = fml  in
                     let uu____71203 =
                       let uu____71204 =
                         let uu____71211 =
                           let uu____71212 =
                             let uu____71225 =
                               let uu____71236 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____71236]  in
                             [uu____71225]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____71212  in
                         (fml, uu____71211)  in
                       FStar_Syntax_Syntax.Tm_meta uu____71204  in
                     {
                       FStar_Syntax_Syntax.n = uu____71203;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_71202.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_71202.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71291 =
                              let uu____71296 =
                                let uu____71297 =
                                  let uu____71306 =
                                    let uu____71307 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71307
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71306  in
                                [uu____71297]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71296
                               in
                            uu____71291 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71364 =
                              let uu____71369 =
                                let uu____71370 =
                                  let uu____71379 =
                                    let uu____71380 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71380
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71379  in
                                [uu____71370]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71369
                               in
                            uu____71364 FStar_Pervasives_Native.None
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
          let uu____71457 =
            let uu____71458 = FStar_Syntax_Subst.compress dt1  in
            uu____71458.FStar_Syntax_Syntax.n  in
          match uu____71457 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____71462) ->
              let dbs1 =
                let uu____71492 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____71492  in
              let dbs2 =
                let uu____71542 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____71542 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____71557 =
                           let uu____71562 =
                             let uu____71563 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____71563]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____71562
                            in
                         uu____71557 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____71596 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____71596 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____71606 =
                       let uu____71611 =
                         let uu____71612 =
                           let uu____71621 =
                             let uu____71622 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____71622
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____71621  in
                         [uu____71612]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____71611
                        in
                     uu____71606 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____71671 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____71762,uu____71763,uu____71764,uu____71765,uu____71766)
                  -> lid
              | uu____71775 -> failwith "Impossible!"  in
            let uu____71777 = acc  in
            match uu____71777 with
            | (uu____71814,en,uu____71816,uu____71817) ->
                let uu____71838 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____71838 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____71875 = acc  in
                     (match uu____71875 with
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
                                     (uu____71950,uu____71951,uu____71952,t_lid,uu____71954,uu____71955)
                                     -> t_lid = lid
                                 | uu____71962 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____71977 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____71977)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____71980 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____71983 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____71980, uu____71983)))
  
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
          let uu____72041 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____72051,us,uu____72053,t,uu____72055,uu____72056) ->
                (us, t)
            | uu____72065 -> failwith "Impossible!"  in
          match uu____72041 with
          | (us,t) ->
              let uu____72075 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____72075 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____72101 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____72101 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____72179 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____72179 with
                           | (uu____72194,t1) ->
                               let uu____72216 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____72216
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____72221 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____72221 with
                          | (phi1,uu____72229) ->
                              ((let uu____72231 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____72231
                                then
                                  let uu____72234 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____72234
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____72252  ->
                                         match uu____72252 with
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
                let uu____72324 =
                  let uu____72325 = FStar_Syntax_Subst.compress t  in
                  uu____72325.FStar_Syntax_Syntax.n  in
                match uu____72324 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____72333) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____72370 = is_mutual t'  in
                    if uu____72370
                    then true
                    else
                      (let uu____72377 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____72377)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____72397) ->
                    is_mutual t'
                | uu____72402 -> false
              
              and exists_mutual uu___586_72404 =
                match uu___586_72404 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____72425 =
                let uu____72426 = FStar_Syntax_Subst.compress dt1  in
                uu____72426.FStar_Syntax_Syntax.n  in
              match uu____72425 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____72432) ->
                  let dbs1 =
                    let uu____72462 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____72462  in
                  let dbs2 =
                    let uu____72512 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____72512 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____72532 =
                               let uu____72537 =
                                 let uu____72538 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____72538]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____72537
                                in
                             uu____72532 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____72570 = is_mutual sort  in
                             if uu____72570
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
                           let uu____72585 =
                             let uu____72590 =
                               let uu____72591 =
                                 let uu____72600 =
                                   let uu____72601 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____72601 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____72600  in
                               [uu____72591]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____72590
                              in
                           uu____72585 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____72650 -> acc
  
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
              let uu____72700 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____72722,bs,t,uu____72725,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____72737 -> failwith "Impossible!"  in
              match uu____72700 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____72761 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____72761 t  in
                  let uu____72770 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____72770 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____72780 =
                           let uu____72781 = FStar_Syntax_Subst.compress t2
                              in
                           uu____72781.FStar_Syntax_Syntax.n  in
                         match uu____72780 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____72785) ->
                             ibs
                         | uu____72806 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____72815 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____72816 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____72815
                           uu____72816
                          in
                       let ind1 =
                         let uu____72822 =
                           let uu____72827 =
                             FStar_List.map
                               (fun uu____72844  ->
                                  match uu____72844 with
                                  | (bv,aq) ->
                                      let uu____72863 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72863, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____72827  in
                         uu____72822 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____72871 =
                           let uu____72876 =
                             FStar_List.map
                               (fun uu____72893  ->
                                  match uu____72893 with
                                  | (bv,aq) ->
                                      let uu____72912 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72912, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____72876  in
                         uu____72871 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____72920 =
                           let uu____72925 =
                             let uu____72926 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____72926]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____72925
                            in
                         uu____72920 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____72965,uu____72966,uu____72967,t_lid,uu____72969,uu____72970)
                                  -> t_lid = lid
                              | uu____72977 -> failwith "Impossible")
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
                         let uu___1460_72989 = fml  in
                         let uu____72990 =
                           let uu____72991 =
                             let uu____72998 =
                               let uu____72999 =
                                 let uu____73012 =
                                   let uu____73023 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____73023]  in
                                 [uu____73012]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____72999
                                in
                             (fml, uu____72998)  in
                           FStar_Syntax_Syntax.Tm_meta uu____72991  in
                         {
                           FStar_Syntax_Syntax.n = uu____72990;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_72989.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_72989.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73078 =
                                  let uu____73083 =
                                    let uu____73084 =
                                      let uu____73093 =
                                        let uu____73094 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73094
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73093
                                       in
                                    [uu____73084]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73083
                                   in
                                uu____73078 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73151 =
                                  let uu____73156 =
                                    let uu____73157 =
                                      let uu____73166 =
                                        let uu____73167 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73167
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73166
                                       in
                                    [uu____73157]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73156
                                   in
                                uu____73151 FStar_Pervasives_Native.None
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
                     (lid,uu____73261,uu____73262,uu____73263,uu____73264,uu____73265)
                     -> lid
                 | uu____73274 -> failwith "Impossible!") tcs
             in
          let uu____73276 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____73288,uu____73289,uu____73290,uu____73291) ->
                (lid, us)
            | uu____73300 -> failwith "Impossible!"  in
          match uu____73276 with
          | (lid,us) ->
              let uu____73310 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____73310 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____73337 =
                       let uu____73338 =
                         let uu____73345 = get_haseq_axiom_lid lid  in
                         (uu____73345, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____73338  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____73337;
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
          let uu____73399 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_73424  ->
                    match uu___587_73424 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____73426;
                        FStar_Syntax_Syntax.sigrng = uu____73427;
                        FStar_Syntax_Syntax.sigquals = uu____73428;
                        FStar_Syntax_Syntax.sigmeta = uu____73429;
                        FStar_Syntax_Syntax.sigattrs = uu____73430;_} -> true
                    | uu____73452 -> false))
             in
          match uu____73399 with
          | (tys,datas) ->
              ((let uu____73475 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_73486  ->
                          match uu___588_73486 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____73488;
                              FStar_Syntax_Syntax.sigrng = uu____73489;
                              FStar_Syntax_Syntax.sigquals = uu____73490;
                              FStar_Syntax_Syntax.sigmeta = uu____73491;
                              FStar_Syntax_Syntax.sigattrs = uu____73492;_}
                              -> false
                          | uu____73513 -> true))
                   in
                if uu____73475
                then
                  let uu____73516 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____73516
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____73531 =
                       let uu____73532 = FStar_List.hd tys  in
                       uu____73532.FStar_Syntax_Syntax.sigel  in
                     match uu____73531 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____73535,uvs,uu____73537,uu____73538,uu____73539,uu____73540)
                         -> uvs
                     | uu____73549 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____73554 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____73584 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____73584 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____73622,bs,t,l1,l2) ->
                                      let uu____73635 =
                                        let uu____73652 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____73653 =
                                          let uu____73654 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____73654 t
                                           in
                                        (lid, univs2, uu____73652,
                                          uu____73653, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____73635
                                  | uu____73667 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_73669 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_73669.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_73669.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_73669.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_73669.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____73679,t,lid_t,x,l) ->
                                      let uu____73690 =
                                        let uu____73706 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____73706, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____73690
                                  | uu____73710 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_73712 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_73712.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_73712.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_73712.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_73712.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____73713 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____73713, tys1, datas1))
                   in
                match uu____73554 with
                | (env1,tys1,datas1) ->
                    let uu____73739 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____73778  ->
                             match uu____73778 with
                             | (env2,all_tcs,g) ->
                                 let uu____73818 = tc_tycon env2 tc  in
                                 (match uu____73818 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____73845 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____73845
                                        then
                                          let uu____73848 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____73848
                                        else ());
                                       (let uu____73853 =
                                          let uu____73854 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____73854
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____73853))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____73739 with
                     | (env2,tcs,g) ->
                         let uu____73900 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____73922  ->
                                  match uu____73922 with
                                  | (datas2,g1) ->
                                      let uu____73941 =
                                        let uu____73946 = tc_data env2 tcs
                                           in
                                        uu____73946 se  in
                                      (match uu____73941 with
                                       | (data,g') ->
                                           let uu____73963 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____73963)))
                             datas1 ([], g)
                            in
                         (match uu____73900 with
                          | (datas2,g1) ->
                              let uu____73984 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____74006 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____74006, datas2))
                                 in
                              (match uu____73984 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____74038 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____74039 =
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
                                         uu____74038;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____74039
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____74065,uu____74066)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____74086 =
                                                    let uu____74092 =
                                                      let uu____74094 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____74096 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____74094
                                                        uu____74096
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____74092)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____74086
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____74100 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____74100 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____74116)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____74147 ->
                                                             let uu____74148
                                                               =
                                                               let uu____74155
                                                                 =
                                                                 let uu____74156
                                                                   =
                                                                   let uu____74171
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____74171)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____74156
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____74155
                                                                in
                                                             uu____74148
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
                                                       let uu____74196 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____74196
                                                        with
                                                        | (uu____74201,inferred)
                                                            ->
                                                            let uu____74203 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____74203
                                                             with
                                                             | (uu____74208,expected)
                                                                 ->
                                                                 let uu____74210
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____74210
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____74217 -> ()));
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
                          let uu____74328 =
                            let uu____74335 =
                              let uu____74336 =
                                let uu____74343 =
                                  let uu____74346 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____74346
                                   in
                                (uu____74343, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____74336  in
                            FStar_Syntax_Syntax.mk uu____74335  in
                          uu____74328 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____74383  ->
                                  match uu____74383 with
                                  | (x,imp) ->
                                      let uu____74402 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____74402, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____74406 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____74406  in
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
                               let uu____74429 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____74429
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____74431 =
                               let uu____74434 =
                                 let uu____74437 =
                                   let uu____74442 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____74443 =
                                     let uu____74444 =
                                       let uu____74453 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____74453
                                        in
                                     [uu____74444]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____74442
                                     uu____74443
                                    in
                                 uu____74437 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____74434  in
                             FStar_Syntax_Util.refine x uu____74431  in
                           let uu____74480 =
                             let uu___1671_74481 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_74481.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_74481.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____74480)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____74498 =
                          FStar_List.map
                            (fun uu____74522  ->
                               match uu____74522 with
                               | (x,uu____74536) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____74498 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____74595  ->
                                match uu____74595 with
                                | (x,uu____74609) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____74620 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____74620)
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
                               (let uu____74641 =
                                  let uu____74643 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____74643.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____74641)
                              in
                           let quals =
                             let uu____74647 =
                               FStar_List.filter
                                 (fun uu___589_74651  ->
                                    match uu___589_74651 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____74656 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____74647
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____74694 =
                                 let uu____74695 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____74695  in
                               FStar_Syntax_Syntax.mk_Total uu____74694  in
                             let uu____74696 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____74696
                              in
                           let decl =
                             let uu____74700 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____74700;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____74702 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____74702
                            then
                              let uu____74706 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____74706
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
                                             fun uu____74767  ->
                                               match uu____74767 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____74796 =
                                                       let uu____74799 =
                                                         let uu____74800 =
                                                           let uu____74807 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____74807,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____74800
                                                          in
                                                       pos uu____74799  in
                                                     (uu____74796, b)
                                                   else
                                                     (let uu____74815 =
                                                        let uu____74818 =
                                                          let uu____74819 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____74819
                                                           in
                                                        pos uu____74818  in
                                                      (uu____74815, b))))
                                      in
                                   let pat_true =
                                     let uu____74838 =
                                       let uu____74841 =
                                         let uu____74842 =
                                           let uu____74856 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____74856, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____74842
                                          in
                                       pos uu____74841  in
                                     (uu____74838,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____74891 =
                                       let uu____74894 =
                                         let uu____74895 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____74895
                                          in
                                       pos uu____74894  in
                                     (uu____74891,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____74909 =
                                     let uu____74916 =
                                       let uu____74917 =
                                         let uu____74940 =
                                           let uu____74957 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____74972 =
                                             let uu____74989 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____74989]  in
                                           uu____74957 :: uu____74972  in
                                         (arg_exp, uu____74940)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____74917
                                        in
                                     FStar_Syntax_Syntax.mk uu____74916  in
                                   uu____74909 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____75068 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____75068
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
                                let uu____75090 =
                                  let uu____75095 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____75095  in
                                let uu____75096 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____75090
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____75096 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____75102 =
                                  let uu____75103 =
                                    let uu____75110 =
                                      let uu____75113 =
                                        let uu____75114 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____75114
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____75113]  in
                                    ((false, [lb]), uu____75110)  in
                                  FStar_Syntax_Syntax.Sig_let uu____75103  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____75102;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____75128 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____75128
                               then
                                 let uu____75132 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____75132
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
                                fun uu____75205  ->
                                  match uu____75205 with
                                  | (a,uu____75214) ->
                                      let uu____75219 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____75219 with
                                       | (field_name,uu____75225) ->
                                           let field_proj_tm =
                                             let uu____75227 =
                                               let uu____75228 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____75228
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____75227 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____75254 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____75296  ->
                                    match uu____75296 with
                                    | (x,uu____75307) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____75313 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____75313 with
                                         | (field_name,uu____75321) ->
                                             let t =
                                               let uu____75325 =
                                                 let uu____75326 =
                                                   let uu____75329 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____75329
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____75326
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____75325
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____75335 =
                                                    let uu____75337 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____75337.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____75335)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____75356 =
                                                   FStar_List.filter
                                                     (fun uu___590_75360  ->
                                                        match uu___590_75360
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____75363 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____75356
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_75378  ->
                                                         match uu___591_75378
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____75384 ->
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
                                               let uu____75395 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____75395;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____75397 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____75397
                                               then
                                                 let uu____75401 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____75401
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
                                                           fun uu____75455 
                                                             ->
                                                             match uu____75455
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
                                                                   let uu____75485
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____75485,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____75505
                                                                    =
                                                                    let uu____75508
                                                                    =
                                                                    let uu____75509
                                                                    =
                                                                    let uu____75516
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____75516,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____75509
                                                                     in
                                                                    pos
                                                                    uu____75508
                                                                     in
                                                                    (uu____75505,
                                                                    b))
                                                                   else
                                                                    (let uu____75524
                                                                    =
                                                                    let uu____75527
                                                                    =
                                                                    let uu____75528
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____75528
                                                                     in
                                                                    pos
                                                                    uu____75527
                                                                     in
                                                                    (uu____75524,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____75547 =
                                                     let uu____75550 =
                                                       let uu____75551 =
                                                         let uu____75565 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____75565,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____75551
                                                        in
                                                     pos uu____75550  in
                                                   let uu____75575 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____75547,
                                                     FStar_Pervasives_Native.None,
                                                     uu____75575)
                                                    in
                                                 let body =
                                                   let uu____75591 =
                                                     let uu____75598 =
                                                       let uu____75599 =
                                                         let uu____75622 =
                                                           let uu____75639 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____75639]  in
                                                         (arg_exp,
                                                           uu____75622)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____75599
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____75598
                                                      in
                                                   uu____75591
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____75707 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____75707
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
                                                   let uu____75726 =
                                                     let uu____75731 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____75731
                                                      in
                                                   let uu____75732 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____75726;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____75732;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____75738 =
                                                     let uu____75739 =
                                                       let uu____75746 =
                                                         let uu____75749 =
                                                           let uu____75750 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____75750
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____75749]  in
                                                       ((false, [lb]),
                                                         uu____75746)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____75739
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____75738;
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
                                                 (let uu____75764 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____75764
                                                  then
                                                    let uu____75768 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____75768
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____75254 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____75822) when
              let uu____75829 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____75829 ->
              let uu____75831 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____75831 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____75853 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____75853 with
                    | (formals,uu____75871) ->
                        let uu____75892 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____75927 =
                                   let uu____75929 =
                                     let uu____75930 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____75930  in
                                   FStar_Ident.lid_equals typ_lid uu____75929
                                    in
                                 if uu____75927
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____75952,uvs',tps,typ0,uu____75956,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____75976 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____76025 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____76025
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____75892 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____76063 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____76063 with
                              | (indices,uu____76081) ->
                                  let refine_domain =
                                    let uu____76104 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_76111  ->
                                              match uu___592_76111 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____76113 -> true
                                              | uu____76123 -> false))
                                       in
                                    if uu____76104
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_76138 =
                                      match uu___593_76138 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____76141,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____76153 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____76154 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____76154 with
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
                                    let uu____76167 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____76167 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____76250  ->
                                               fun uu____76251  ->
                                                 match (uu____76250,
                                                         uu____76251)
                                                 with
                                                 | ((x,uu____76277),(x',uu____76279))
                                                     ->
                                                     let uu____76300 =
                                                       let uu____76307 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____76307)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____76300) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____76312 -> []
  