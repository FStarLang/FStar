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
          let uu____66275 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____66275 with
           | (usubst,uvs1) ->
               let uu____66302 =
                 let uu____66309 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____66310 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____66311 =
                   let uu____66312 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____66312 k  in
                 (uu____66309, uu____66310, uu____66311)  in
               (match uu____66302 with
                | (env1,tps1,k1) ->
                    let uu____66332 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____66332 with
                     | (tps2,k2) ->
                         let uu____66347 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____66347 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____66368 =
                                let uu____66387 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____66387 with
                                | (k3,uu____66413,g) ->
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
                                    let uu____66416 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____66431 =
                                      let uu____66432 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____66432
                                       in
                                    (uu____66416, uu____66431)
                                 in
                              (match uu____66368 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____66495 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____66495
                                      in
                                   let uu____66498 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____66498 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____66516 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____66516))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____66523 =
                                              let uu____66529 =
                                                let uu____66531 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____66533 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____66531 uu____66533
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____66529)
                                               in
                                            FStar_Errors.raise_error
                                              uu____66523
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
                                            let uu____66546 =
                                              let uu____66555 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____66572 =
                                                let uu____66581 =
                                                  let uu____66594 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____66594
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____66581
                                                 in
                                              FStar_List.append uu____66555
                                                uu____66572
                                               in
                                            let uu____66617 =
                                              let uu____66620 =
                                                let uu____66621 =
                                                  let uu____66626 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____66626
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____66621
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____66620
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____66546 uu____66617
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____66643 =
                                            let uu____66648 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____66649 =
                                              let uu____66650 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____66650 k4
                                               in
                                            (uu____66648, uu____66649)  in
                                          match uu____66643 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____66670 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____66670,
                                                (let uu___646_66676 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_66676.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_66676.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_66676.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_66676.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____66681 -> failwith "impossible"
  
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
            let uu____66745 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____66745 with
             | (usubst,_uvs1) ->
                 let uu____66768 =
                   let uu____66773 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____66774 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____66773, uu____66774)  in
                 (match uu____66768 with
                  | (env1,t1) ->
                      let uu____66781 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____66820  ->
                               match uu____66820 with
                               | (se1,u_tc) ->
                                   let uu____66835 =
                                     let uu____66837 =
                                       let uu____66838 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____66838  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____66837
                                      in
                                   if uu____66835
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____66858,uu____66859,tps,uu____66861,uu____66862,uu____66863)
                                          ->
                                          let tps1 =
                                            let uu____66873 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____66873
                                              (FStar_List.map
                                                 (fun uu____66913  ->
                                                    match uu____66913 with
                                                    | (x,uu____66927) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____66935 =
                                            let uu____66942 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____66942, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____66935
                                      | uu____66949 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____66992 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____66992
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____66781 with
                       | (env2,tps,u_tc) ->
                           let uu____67024 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____67040 =
                               let uu____67041 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____67041.FStar_Syntax_Syntax.n  in
                             match uu____67040 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____67080 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____67080 with
                                  | (uu____67121,bs') ->
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
                                                fun uu____67192  ->
                                                  match uu____67192 with
                                                  | (x,uu____67201) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____67208 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____67208)
                             | uu____67209 -> ([], t2)  in
                           (match uu____67024 with
                            | (arguments,result) ->
                                ((let uu____67253 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____67253
                                  then
                                    let uu____67256 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____67258 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____67261 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____67256 uu____67258 uu____67261
                                  else ());
                                 (let uu____67266 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____67266 with
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
                                      let uu____67284 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____67284 with
                                       | (result1,res_lcomp) ->
                                           let uu____67295 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____67295 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____67353 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____67353
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____67435  ->
                                                      fun uu____67436  ->
                                                        match (uu____67435,
                                                                uu____67436)
                                                        with
                                                        | ((bv,uu____67466),
                                                           (t2,uu____67468))
                                                            ->
                                                            let uu____67495 =
                                                              let uu____67496
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____67496.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____67495
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____67500 ->
                                                                 let uu____67501
                                                                   =
                                                                   let uu____67507
                                                                    =
                                                                    let uu____67509
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____67511
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____67509
                                                                    uu____67511
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____67507)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____67501
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____67516 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____67516
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____67518 =
                                                     let uu____67519 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____67519.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____67518 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____67522 -> ()
                                                   | uu____67523 ->
                                                       let uu____67524 =
                                                         let uu____67530 =
                                                           let uu____67532 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____67534 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____67532
                                                             uu____67534
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____67530)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____67524
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____67539 =
                                                       let uu____67540 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____67540.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____67539 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____67544;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____67545;_},tuvs)
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
                                                                    let uu____67559
                                                                    =
                                                                    let uu____67560
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____67561
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
                                                                    uu____67560
                                                                    uu____67561
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67559)
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
                                                     | uu____67567 ->
                                                         let uu____67568 =
                                                           let uu____67574 =
                                                             let uu____67576
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____67578
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____67576
                                                               uu____67578
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____67574)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____67568
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____67596  ->
                                                            fun u_x  ->
                                                              match uu____67596
                                                              with
                                                              | (x,uu____67605)
                                                                  ->
                                                                  let uu____67610
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67610)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____67614 =
                                                       let uu____67623 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____67663 
                                                                 ->
                                                                 match uu____67663
                                                                 with
                                                                 | (x,uu____67677)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____67623
                                                         arguments1
                                                        in
                                                     let uu____67691 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____67614
                                                       uu____67691
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_67696 = se
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
                                                         (uu___768_67696.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_67696.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_67696.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_67696.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____67700 -> failwith "impossible"
  
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
            let uu___776_67767 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_67767.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_67767.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_67767.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____67777 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____67777
           then
             let uu____67782 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____67782
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____67825  ->
                     match uu____67825 with
                     | (se,uu____67831) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____67832,uu____67833,tps,k,uu____67836,uu____67837)
                              ->
                              let uu____67846 =
                                let uu____67847 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____67847
                                 in
                              FStar_Syntax_Syntax.null_binder uu____67846
                          | uu____67852 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____67881,uu____67882,t,uu____67884,uu____67885,uu____67886)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____67893 -> failwith "Impossible"))
              in
           let t =
             let uu____67898 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____67898
              in
           (let uu____67908 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____67908
            then
              let uu____67913 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____67913
            else ());
           (let uu____67918 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____67918 with
            | (uvs,t1) ->
                ((let uu____67938 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____67938
                  then
                    let uu____67943 =
                      let uu____67945 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____67945
                        (FStar_String.concat ", ")
                       in
                    let uu____67962 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____67943 uu____67962
                  else ());
                 (let uu____67967 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____67967 with
                  | (uvs1,t2) ->
                      let uu____67982 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____67982 with
                       | (args,uu____68006) ->
                           let uu____68027 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____68027 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____68132  ->
                                       fun uu____68133  ->
                                         match (uu____68132, uu____68133)
                                         with
                                         | ((x,uu____68155),(se,uu____68157))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____68173,tps,uu____68175,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____68187 =
                                                    let uu____68192 =
                                                      let uu____68193 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____68193.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____68192 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____68222 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____68222
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____68300
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____68319 -> ([], ty)
                                                     in
                                                  (match uu____68187 with
                                                   | (tps1,t3) ->
                                                       let uu___853_68328 =
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
                                                           (uu___853_68328.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_68328.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_68328.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_68328.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____68333 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____68340 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _68344  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _68344))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_68363  ->
                                                match uu___585_68363 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____68369,uu____68370,uu____68371,uu____68372,uu____68373);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____68374;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____68375;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____68376;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____68377;_}
                                                    -> (tc, uvs_universes)
                                                | uu____68390 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____68414  ->
                                           fun d  ->
                                             match uu____68414 with
                                             | (t3,uu____68423) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____68429,uu____68430,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____68441 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____68441
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_68442 = d
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
                                                          (uu___889_68442.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_68442.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_68442.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_68442.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____68446 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____68465 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____68465
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____68487 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____68487
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____68504 =
      let uu____68505 = FStar_Syntax_Subst.compress t  in
      uu____68505.FStar_Syntax_Syntax.n  in
    match uu____68504 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____68524 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____68530 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____68587 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____68656  ->
               match uu____68656 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____68700 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____68700  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____68587
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____68955 =
             let uu____68957 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____68957
              in
           debug_log env uu____68955);
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
           (let uu____68962 =
              let uu____68964 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____68964
               in
            debug_log env uu____68962);
           (let uu____68969 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____68969) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____68982 =
                  let uu____68983 = FStar_Syntax_Subst.compress btype1  in
                  uu____68983.FStar_Syntax_Syntax.n  in
                match uu____68982 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____69013 = try_get_fv t  in
                    (match uu____69013 with
                     | (fv,us) ->
                         let uu____69021 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____69021
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____69037  ->
                                 match uu____69037 with
                                 | (t1,uu____69046) ->
                                     let uu____69051 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____69051) args)
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
                          let uu____69106 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____69106
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____69110 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____69110
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
                            (fun uu____69137  ->
                               match uu____69137 with
                               | (b,uu____69146) ->
                                   let uu____69151 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____69151) sbs)
                           &&
                           ((let uu____69157 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____69157 with
                             | (uu____69163,return_type) ->
                                 let uu____69165 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____69165)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____69186 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____69190 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____69195) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____69223) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____69250,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____69309  ->
                          match uu____69309 with
                          | (p,uu____69322,t) ->
                              let bs =
                                let uu____69341 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____69341
                                 in
                              let uu____69350 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____69350 with
                               | (bs1,t1) ->
                                   let uu____69358 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____69358)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____69380,uu____69381)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____69444 ->
                    ((let uu____69446 =
                        let uu____69448 =
                          let uu____69450 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____69452 =
                            let uu____69454 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____69454  in
                          Prims.op_Hat uu____69450 uu____69452  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____69448
                         in
                      debug_log env uu____69446);
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
              (let uu____69477 =
                 let uu____69479 =
                   let uu____69481 =
                     let uu____69483 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____69483  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____69481  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____69479
                  in
               debug_log env uu____69477);
              (let uu____69487 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____69487 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____69506 =
                       let uu____69508 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____69508
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____69506
                      then
                        ((let uu____69512 =
                            let uu____69514 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____69514
                             in
                          debug_log env uu____69512);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____69525 =
                        already_unfolded ilid args unfolded env  in
                      if uu____69525
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____69556 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____69556  in
                         (let uu____69562 =
                            let uu____69564 =
                              let uu____69566 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____69566
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____69564
                             in
                          debug_log env uu____69562);
                         (let uu____69571 =
                            let uu____69572 = FStar_ST.op_Bang unfolded  in
                            let uu____69618 =
                              let uu____69625 =
                                let uu____69630 =
                                  let uu____69631 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____69631  in
                                (ilid, uu____69630)  in
                              [uu____69625]  in
                            FStar_List.append uu____69572 uu____69618  in
                          FStar_ST.op_Colon_Equals unfolded uu____69571);
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
                  (let uu____69780 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____69780 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____69803 ->
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
                         (let uu____69807 =
                            let uu____69809 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____69809
                             in
                          debug_log env uu____69807);
                         (let uu____69812 =
                            let uu____69813 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____69813.FStar_Syntax_Syntax.n  in
                          match uu____69812 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____69841 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____69841 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____69905 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____69905 dbs1
                                       in
                                    let c1 =
                                      let uu____69909 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____69909 c
                                       in
                                    let uu____69912 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____69912 with
                                     | (args1,uu____69947) ->
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
                                           let uu____70039 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____70039 c1
                                            in
                                         ((let uu____70049 =
                                             let uu____70051 =
                                               let uu____70053 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____70056 =
                                                 let uu____70058 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____70058
                                                  in
                                               Prims.op_Hat uu____70053
                                                 uu____70056
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____70051
                                              in
                                           debug_log env uu____70049);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____70092 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____70095 =
                                  let uu____70096 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____70096.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____70095
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
                   (let uu____70165 = try_get_fv t1  in
                    match uu____70165 with
                    | (fv,uu____70172) ->
                        let uu____70173 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____70173
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____70205 =
                      let uu____70207 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____70207
                       in
                    debug_log env uu____70205);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____70212 =
                      FStar_List.fold_left
                        (fun uu____70233  ->
                           fun b  ->
                             match uu____70233 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____70264 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____70288 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____70264, uu____70288))) (true, env)
                        sbs1
                       in
                    match uu____70212 with | (b,uu____70306) -> b))
              | uu____70309 ->
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
              let uu____70365 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____70365 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____70388 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____70391 =
                      let uu____70393 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____70393
                       in
                    debug_log env uu____70391);
                   (let uu____70396 =
                      let uu____70397 = FStar_Syntax_Subst.compress dt  in
                      uu____70397.FStar_Syntax_Syntax.n  in
                    match uu____70396 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____70401 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____70406) ->
                        let dbs1 =
                          let uu____70436 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____70436  in
                        let dbs2 =
                          let uu____70486 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____70486 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____70491 =
                            let uu____70493 =
                              let uu____70495 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____70495 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____70493
                             in
                          debug_log env uu____70491);
                         (let uu____70505 =
                            FStar_List.fold_left
                              (fun uu____70526  ->
                                 fun b  ->
                                   match uu____70526 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____70557 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____70581 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____70557, uu____70581)))
                              (true, env) dbs3
                             in
                          match uu____70505 with | (b,uu____70599) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____70602,uu____70603) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____70659 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____70682 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____70698,uu____70699,uu____70700) -> (lid, us, bs)
        | uu____70709 -> failwith "Impossible!"  in
      match uu____70682 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____70721 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____70721 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____70745 =
                 let uu____70748 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____70748  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____70762 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____70762
                      unfolded_inductives env2) uu____70745)
  
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
        (uu____70841,uu____70842,t,uu____70844,uu____70845,uu____70846) -> t
    | uu____70853 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____70880 =
         let uu____70882 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____70882 haseq_suffix  in
       uu____70880 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____70906 =
      let uu____70909 =
        let uu____70912 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____70912]  in
      FStar_List.append lid.FStar_Ident.ns uu____70909  in
    FStar_Ident.lid_of_ids uu____70906
  
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
          let uu____70958 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____70972,bs,t,uu____70975,uu____70976) ->
                (lid, bs, t)
            | uu____70985 -> failwith "Impossible!"  in
          match uu____70958 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____71008 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____71008 t  in
              let uu____71017 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____71017 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____71035 =
                       let uu____71036 = FStar_Syntax_Subst.compress t2  in
                       uu____71036.FStar_Syntax_Syntax.n  in
                     match uu____71035 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____71040) -> ibs
                     | uu____71061 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____71070 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____71071 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____71070 uu____71071
                      in
                   let ind1 =
                     let uu____71077 =
                       let uu____71082 =
                         FStar_List.map
                           (fun uu____71099  ->
                              match uu____71099 with
                              | (bv,aq) ->
                                  let uu____71118 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71118, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____71082  in
                     uu____71077 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____71126 =
                       let uu____71131 =
                         FStar_List.map
                           (fun uu____71148  ->
                              match uu____71148 with
                              | (bv,aq) ->
                                  let uu____71167 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71167, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____71131  in
                     uu____71126 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____71175 =
                       let uu____71180 =
                         let uu____71181 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____71181]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____71180
                        in
                     uu____71175 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____71232 =
                            let uu____71233 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____71233  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____71232) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____71246 =
                              let uu____71249 =
                                let uu____71254 =
                                  let uu____71255 =
                                    let uu____71264 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____71264
                                     in
                                  [uu____71255]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____71254
                                 in
                              uu____71249 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____71246)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_71289 = fml  in
                     let uu____71290 =
                       let uu____71291 =
                         let uu____71298 =
                           let uu____71299 =
                             let uu____71312 =
                               let uu____71323 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____71323]  in
                             [uu____71312]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____71299  in
                         (fml, uu____71298)  in
                       FStar_Syntax_Syntax.Tm_meta uu____71291  in
                     {
                       FStar_Syntax_Syntax.n = uu____71290;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_71289.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_71289.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71378 =
                              let uu____71383 =
                                let uu____71384 =
                                  let uu____71393 =
                                    let uu____71394 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71394
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71393  in
                                [uu____71384]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71383
                               in
                            uu____71378 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71451 =
                              let uu____71456 =
                                let uu____71457 =
                                  let uu____71466 =
                                    let uu____71467 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71467
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71466  in
                                [uu____71457]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71456
                               in
                            uu____71451 FStar_Pervasives_Native.None
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
          let uu____71544 =
            let uu____71545 = FStar_Syntax_Subst.compress dt1  in
            uu____71545.FStar_Syntax_Syntax.n  in
          match uu____71544 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____71549) ->
              let dbs1 =
                let uu____71579 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____71579  in
              let dbs2 =
                let uu____71629 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____71629 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____71644 =
                           let uu____71649 =
                             let uu____71650 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____71650]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____71649
                            in
                         uu____71644 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____71683 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____71683 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____71693 =
                       let uu____71698 =
                         let uu____71699 =
                           let uu____71708 =
                             let uu____71709 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____71709
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____71708  in
                         [uu____71699]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____71698
                        in
                     uu____71693 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____71758 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____71849,uu____71850,uu____71851,uu____71852,uu____71853)
                  -> lid
              | uu____71862 -> failwith "Impossible!"  in
            let uu____71864 = acc  in
            match uu____71864 with
            | (uu____71901,en,uu____71903,uu____71904) ->
                let uu____71925 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____71925 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____71962 = acc  in
                     (match uu____71962 with
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
                                     (uu____72037,uu____72038,uu____72039,t_lid,uu____72041,uu____72042)
                                     -> t_lid = lid
                                 | uu____72049 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____72064 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____72064)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____72067 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____72070 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____72067, uu____72070)))
  
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
          let uu____72128 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____72138,us,uu____72140,t,uu____72142,uu____72143) ->
                (us, t)
            | uu____72152 -> failwith "Impossible!"  in
          match uu____72128 with
          | (us,t) ->
              let uu____72162 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____72162 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____72188 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____72188 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____72266 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____72266 with
                           | (uu____72281,t1) ->
                               let uu____72303 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____72303
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____72308 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____72308 with
                          | (phi1,uu____72316) ->
                              ((let uu____72318 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____72318
                                then
                                  let uu____72321 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____72321
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____72339  ->
                                         match uu____72339 with
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
                let uu____72411 =
                  let uu____72412 = FStar_Syntax_Subst.compress t  in
                  uu____72412.FStar_Syntax_Syntax.n  in
                match uu____72411 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____72420) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____72457 = is_mutual t'  in
                    if uu____72457
                    then true
                    else
                      (let uu____72464 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____72464)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____72484) ->
                    is_mutual t'
                | uu____72489 -> false
              
              and exists_mutual uu___586_72491 =
                match uu___586_72491 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____72512 =
                let uu____72513 = FStar_Syntax_Subst.compress dt1  in
                uu____72513.FStar_Syntax_Syntax.n  in
              match uu____72512 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____72519) ->
                  let dbs1 =
                    let uu____72549 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____72549  in
                  let dbs2 =
                    let uu____72599 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____72599 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____72619 =
                               let uu____72624 =
                                 let uu____72625 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____72625]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____72624
                                in
                             uu____72619 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____72657 = is_mutual sort  in
                             if uu____72657
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
                           let uu____72672 =
                             let uu____72677 =
                               let uu____72678 =
                                 let uu____72687 =
                                   let uu____72688 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____72688 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____72687  in
                               [uu____72678]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____72677
                              in
                           uu____72672 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____72737 -> acc
  
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
              let uu____72787 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____72809,bs,t,uu____72812,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____72824 -> failwith "Impossible!"  in
              match uu____72787 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____72848 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____72848 t  in
                  let uu____72857 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____72857 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____72867 =
                           let uu____72868 = FStar_Syntax_Subst.compress t2
                              in
                           uu____72868.FStar_Syntax_Syntax.n  in
                         match uu____72867 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____72872) ->
                             ibs
                         | uu____72893 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____72902 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____72903 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____72902
                           uu____72903
                          in
                       let ind1 =
                         let uu____72909 =
                           let uu____72914 =
                             FStar_List.map
                               (fun uu____72931  ->
                                  match uu____72931 with
                                  | (bv,aq) ->
                                      let uu____72950 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72950, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____72914  in
                         uu____72909 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____72958 =
                           let uu____72963 =
                             FStar_List.map
                               (fun uu____72980  ->
                                  match uu____72980 with
                                  | (bv,aq) ->
                                      let uu____72999 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72999, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____72963  in
                         uu____72958 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____73007 =
                           let uu____73012 =
                             let uu____73013 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____73013]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____73012
                            in
                         uu____73007 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____73052,uu____73053,uu____73054,t_lid,uu____73056,uu____73057)
                                  -> t_lid = lid
                              | uu____73064 -> failwith "Impossible")
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
                         let uu___1460_73076 = fml  in
                         let uu____73077 =
                           let uu____73078 =
                             let uu____73085 =
                               let uu____73086 =
                                 let uu____73099 =
                                   let uu____73110 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____73110]  in
                                 [uu____73099]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____73086
                                in
                             (fml, uu____73085)  in
                           FStar_Syntax_Syntax.Tm_meta uu____73078  in
                         {
                           FStar_Syntax_Syntax.n = uu____73077;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_73076.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_73076.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73165 =
                                  let uu____73170 =
                                    let uu____73171 =
                                      let uu____73180 =
                                        let uu____73181 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73181
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73180
                                       in
                                    [uu____73171]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73170
                                   in
                                uu____73165 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73238 =
                                  let uu____73243 =
                                    let uu____73244 =
                                      let uu____73253 =
                                        let uu____73254 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73254
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73253
                                       in
                                    [uu____73244]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73243
                                   in
                                uu____73238 FStar_Pervasives_Native.None
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
                     (lid,uu____73348,uu____73349,uu____73350,uu____73351,uu____73352)
                     -> lid
                 | uu____73361 -> failwith "Impossible!") tcs
             in
          let uu____73363 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____73375,uu____73376,uu____73377,uu____73378) ->
                (lid, us)
            | uu____73387 -> failwith "Impossible!"  in
          match uu____73363 with
          | (lid,us) ->
              let uu____73397 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____73397 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____73424 =
                       let uu____73425 =
                         let uu____73432 = get_haseq_axiom_lid lid  in
                         (uu____73432, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____73425  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____73424;
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
          let uu____73486 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_73511  ->
                    match uu___587_73511 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____73513;
                        FStar_Syntax_Syntax.sigrng = uu____73514;
                        FStar_Syntax_Syntax.sigquals = uu____73515;
                        FStar_Syntax_Syntax.sigmeta = uu____73516;
                        FStar_Syntax_Syntax.sigattrs = uu____73517;_} -> true
                    | uu____73539 -> false))
             in
          match uu____73486 with
          | (tys,datas) ->
              ((let uu____73562 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_73573  ->
                          match uu___588_73573 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____73575;
                              FStar_Syntax_Syntax.sigrng = uu____73576;
                              FStar_Syntax_Syntax.sigquals = uu____73577;
                              FStar_Syntax_Syntax.sigmeta = uu____73578;
                              FStar_Syntax_Syntax.sigattrs = uu____73579;_}
                              -> false
                          | uu____73600 -> true))
                   in
                if uu____73562
                then
                  let uu____73603 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____73603
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____73618 =
                       let uu____73619 = FStar_List.hd tys  in
                       uu____73619.FStar_Syntax_Syntax.sigel  in
                     match uu____73618 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____73622,uvs,uu____73624,uu____73625,uu____73626,uu____73627)
                         -> uvs
                     | uu____73636 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____73641 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____73671 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____73671 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____73709,bs,t,l1,l2) ->
                                      let uu____73722 =
                                        let uu____73739 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____73740 =
                                          let uu____73741 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____73741 t
                                           in
                                        (lid, univs2, uu____73739,
                                          uu____73740, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____73722
                                  | uu____73754 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_73756 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_73756.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_73756.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_73756.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_73756.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____73766,t,lid_t,x,l) ->
                                      let uu____73777 =
                                        let uu____73793 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____73793, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____73777
                                  | uu____73797 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_73799 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_73799.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_73799.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_73799.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_73799.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____73800 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____73800, tys1, datas1))
                   in
                match uu____73641 with
                | (env1,tys1,datas1) ->
                    let uu____73826 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____73865  ->
                             match uu____73865 with
                             | (env2,all_tcs,g) ->
                                 let uu____73905 = tc_tycon env2 tc  in
                                 (match uu____73905 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____73932 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____73932
                                        then
                                          let uu____73935 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____73935
                                        else ());
                                       (let uu____73940 =
                                          let uu____73941 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____73941
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____73940))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____73826 with
                     | (env2,tcs,g) ->
                         let uu____73987 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____74009  ->
                                  match uu____74009 with
                                  | (datas2,g1) ->
                                      let uu____74028 =
                                        let uu____74033 = tc_data env2 tcs
                                           in
                                        uu____74033 se  in
                                      (match uu____74028 with
                                       | (data,g') ->
                                           let uu____74050 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____74050)))
                             datas1 ([], g)
                            in
                         (match uu____73987 with
                          | (datas2,g1) ->
                              let uu____74071 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____74093 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____74093, datas2))
                                 in
                              (match uu____74071 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____74125 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____74126 =
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
                                         uu____74125;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____74126
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____74152,uu____74153)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____74173 =
                                                    let uu____74179 =
                                                      let uu____74181 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____74183 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____74181
                                                        uu____74183
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____74179)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____74173
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____74187 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____74187 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____74203)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____74234 ->
                                                             let uu____74235
                                                               =
                                                               let uu____74242
                                                                 =
                                                                 let uu____74243
                                                                   =
                                                                   let uu____74258
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____74258)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____74243
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____74242
                                                                in
                                                             uu____74235
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
                                                       let uu____74283 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____74283
                                                        with
                                                        | (uu____74288,inferred)
                                                            ->
                                                            let uu____74290 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____74290
                                                             with
                                                             | (uu____74295,expected)
                                                                 ->
                                                                 let uu____74297
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____74297
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____74304 -> ()));
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
                          let uu____74415 =
                            let uu____74422 =
                              let uu____74423 =
                                let uu____74430 =
                                  let uu____74433 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____74433
                                   in
                                (uu____74430, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____74423  in
                            FStar_Syntax_Syntax.mk uu____74422  in
                          uu____74415 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____74470  ->
                                  match uu____74470 with
                                  | (x,imp) ->
                                      let uu____74489 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____74489, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____74493 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____74493  in
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
                               let uu____74516 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____74516
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____74518 =
                               let uu____74521 =
                                 let uu____74524 =
                                   let uu____74529 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____74530 =
                                     let uu____74531 =
                                       let uu____74540 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____74540
                                        in
                                     [uu____74531]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____74529
                                     uu____74530
                                    in
                                 uu____74524 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____74521  in
                             FStar_Syntax_Util.refine x uu____74518  in
                           let uu____74567 =
                             let uu___1671_74568 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_74568.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_74568.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____74567)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____74585 =
                          FStar_List.map
                            (fun uu____74609  ->
                               match uu____74609 with
                               | (x,uu____74623) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____74585 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____74682  ->
                                match uu____74682 with
                                | (x,uu____74696) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____74707 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____74707)
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
                               (let uu____74728 =
                                  let uu____74730 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____74730.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____74728)
                              in
                           let quals =
                             let uu____74734 =
                               FStar_List.filter
                                 (fun uu___589_74738  ->
                                    match uu___589_74738 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____74743 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____74734
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____74781 =
                                 let uu____74782 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____74782  in
                               FStar_Syntax_Syntax.mk_Total uu____74781  in
                             let uu____74783 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____74783
                              in
                           let decl =
                             let uu____74787 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____74787;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____74789 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____74789
                            then
                              let uu____74793 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____74793
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
                                             fun uu____74854  ->
                                               match uu____74854 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____74883 =
                                                       let uu____74886 =
                                                         let uu____74887 =
                                                           let uu____74894 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____74894,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____74887
                                                          in
                                                       pos uu____74886  in
                                                     (uu____74883, b)
                                                   else
                                                     (let uu____74902 =
                                                        let uu____74905 =
                                                          let uu____74906 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____74906
                                                           in
                                                        pos uu____74905  in
                                                      (uu____74902, b))))
                                      in
                                   let pat_true =
                                     let uu____74925 =
                                       let uu____74928 =
                                         let uu____74929 =
                                           let uu____74943 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____74943, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____74929
                                          in
                                       pos uu____74928  in
                                     (uu____74925,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____74978 =
                                       let uu____74981 =
                                         let uu____74982 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____74982
                                          in
                                       pos uu____74981  in
                                     (uu____74978,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____74996 =
                                     let uu____75003 =
                                       let uu____75004 =
                                         let uu____75027 =
                                           let uu____75044 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____75059 =
                                             let uu____75076 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____75076]  in
                                           uu____75044 :: uu____75059  in
                                         (arg_exp, uu____75027)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____75004
                                        in
                                     FStar_Syntax_Syntax.mk uu____75003  in
                                   uu____74996 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____75155 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____75155
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
                                let uu____75177 =
                                  let uu____75182 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____75182  in
                                let uu____75183 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____75177
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____75183 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____75189 =
                                  let uu____75190 =
                                    let uu____75197 =
                                      let uu____75200 =
                                        let uu____75201 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____75201
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____75200]  in
                                    ((false, [lb]), uu____75197)  in
                                  FStar_Syntax_Syntax.Sig_let uu____75190  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____75189;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____75215 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____75215
                               then
                                 let uu____75219 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____75219
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
                                fun uu____75292  ->
                                  match uu____75292 with
                                  | (a,uu____75301) ->
                                      let uu____75306 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____75306 with
                                       | (field_name,uu____75312) ->
                                           let field_proj_tm =
                                             let uu____75314 =
                                               let uu____75315 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____75315
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____75314 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____75341 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____75383  ->
                                    match uu____75383 with
                                    | (x,uu____75394) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____75400 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____75400 with
                                         | (field_name,uu____75408) ->
                                             let t =
                                               let uu____75412 =
                                                 let uu____75413 =
                                                   let uu____75416 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____75416
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____75413
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____75412
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____75422 =
                                                    let uu____75424 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____75424.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____75422)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____75443 =
                                                   FStar_List.filter
                                                     (fun uu___590_75447  ->
                                                        match uu___590_75447
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____75450 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____75443
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_75465  ->
                                                         match uu___591_75465
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____75471 ->
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
                                               let uu____75482 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____75482;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____75484 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____75484
                                               then
                                                 let uu____75488 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____75488
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
                                                           fun uu____75542 
                                                             ->
                                                             match uu____75542
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
                                                                   let uu____75572
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____75572,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____75592
                                                                    =
                                                                    let uu____75595
                                                                    =
                                                                    let uu____75596
                                                                    =
                                                                    let uu____75603
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____75603,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____75596
                                                                     in
                                                                    pos
                                                                    uu____75595
                                                                     in
                                                                    (uu____75592,
                                                                    b))
                                                                   else
                                                                    (let uu____75611
                                                                    =
                                                                    let uu____75614
                                                                    =
                                                                    let uu____75615
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____75615
                                                                     in
                                                                    pos
                                                                    uu____75614
                                                                     in
                                                                    (uu____75611,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____75634 =
                                                     let uu____75637 =
                                                       let uu____75638 =
                                                         let uu____75652 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____75652,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____75638
                                                        in
                                                     pos uu____75637  in
                                                   let uu____75662 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____75634,
                                                     FStar_Pervasives_Native.None,
                                                     uu____75662)
                                                    in
                                                 let body =
                                                   let uu____75678 =
                                                     let uu____75685 =
                                                       let uu____75686 =
                                                         let uu____75709 =
                                                           let uu____75726 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____75726]  in
                                                         (arg_exp,
                                                           uu____75709)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____75686
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____75685
                                                      in
                                                   uu____75678
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____75794 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____75794
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
                                                   let uu____75813 =
                                                     let uu____75818 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____75818
                                                      in
                                                   let uu____75819 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____75813;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____75819;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____75825 =
                                                     let uu____75826 =
                                                       let uu____75833 =
                                                         let uu____75836 =
                                                           let uu____75837 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____75837
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____75836]  in
                                                       ((false, [lb]),
                                                         uu____75833)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____75826
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____75825;
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
                                                 (let uu____75851 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____75851
                                                  then
                                                    let uu____75855 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____75855
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____75341 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____75909) when
              let uu____75916 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____75916 ->
              let uu____75918 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____75918 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____75940 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____75940 with
                    | (formals,uu____75958) ->
                        let uu____75979 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____76014 =
                                   let uu____76016 =
                                     let uu____76017 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____76017  in
                                   FStar_Ident.lid_equals typ_lid uu____76016
                                    in
                                 if uu____76014
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____76039,uvs',tps,typ0,uu____76043,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____76063 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____76112 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____76112
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____75979 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____76150 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____76150 with
                              | (indices,uu____76168) ->
                                  let refine_domain =
                                    let uu____76191 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_76198  ->
                                              match uu___592_76198 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____76200 -> true
                                              | uu____76210 -> false))
                                       in
                                    if uu____76191
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_76225 =
                                      match uu___593_76225 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____76228,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____76240 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____76241 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____76241 with
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
                                    let uu____76254 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____76254 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____76337  ->
                                               fun uu____76338  ->
                                                 match (uu____76337,
                                                         uu____76338)
                                                 with
                                                 | ((x,uu____76364),(x',uu____76366))
                                                     ->
                                                     let uu____76387 =
                                                       let uu____76394 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____76394)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____76387) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____76399 -> []
  