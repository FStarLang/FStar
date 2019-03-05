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
          let uu____66303 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____66303 with
           | (usubst,uvs1) ->
               let uu____66330 =
                 let uu____66337 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____66338 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____66339 =
                   let uu____66340 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____66340 k  in
                 (uu____66337, uu____66338, uu____66339)  in
               (match uu____66330 with
                | (env1,tps1,k1) ->
                    let uu____66360 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____66360 with
                     | (tps2,k2) ->
                         let uu____66375 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____66375 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____66396 =
                                let uu____66415 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____66415 with
                                | (k3,uu____66441,g) ->
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
                                    let uu____66444 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____66459 =
                                      let uu____66460 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____66460
                                       in
                                    (uu____66444, uu____66459)
                                 in
                              (match uu____66396 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____66523 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____66523
                                      in
                                   let uu____66526 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____66526 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____66544 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____66544))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____66551 =
                                              let uu____66557 =
                                                let uu____66559 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____66561 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____66559 uu____66561
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____66557)
                                               in
                                            FStar_Errors.raise_error
                                              uu____66551
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
                                            let uu____66574 =
                                              let uu____66583 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____66600 =
                                                let uu____66609 =
                                                  let uu____66622 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____66622
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____66609
                                                 in
                                              FStar_List.append uu____66583
                                                uu____66600
                                               in
                                            let uu____66645 =
                                              let uu____66648 =
                                                let uu____66649 =
                                                  let uu____66654 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____66654
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____66649
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____66648
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____66574 uu____66645
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____66671 =
                                            let uu____66676 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____66677 =
                                              let uu____66678 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____66678 k4
                                               in
                                            (uu____66676, uu____66677)  in
                                          match uu____66671 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____66698 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____66698,
                                                (let uu___646_66704 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_66704.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_66704.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_66704.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_66704.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____66709 -> failwith "impossible"
  
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
            let uu____66773 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____66773 with
             | (usubst,_uvs1) ->
                 let uu____66796 =
                   let uu____66801 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____66802 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____66801, uu____66802)  in
                 (match uu____66796 with
                  | (env1,t1) ->
                      let uu____66809 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____66848  ->
                               match uu____66848 with
                               | (se1,u_tc) ->
                                   let uu____66863 =
                                     let uu____66865 =
                                       let uu____66866 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____66866  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____66865
                                      in
                                   if uu____66863
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____66886,uu____66887,tps,uu____66889,uu____66890,uu____66891)
                                          ->
                                          let tps1 =
                                            let uu____66901 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____66901
                                              (FStar_List.map
                                                 (fun uu____66941  ->
                                                    match uu____66941 with
                                                    | (x,uu____66955) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____66963 =
                                            let uu____66970 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____66970, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____66963
                                      | uu____66977 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____67020 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____67020
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____66809 with
                       | (env2,tps,u_tc) ->
                           let uu____67052 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____67068 =
                               let uu____67069 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____67069.FStar_Syntax_Syntax.n  in
                             match uu____67068 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____67108 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____67108 with
                                  | (uu____67149,bs') ->
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
                                                fun uu____67220  ->
                                                  match uu____67220 with
                                                  | (x,uu____67229) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____67236 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____67236)
                             | uu____67237 -> ([], t2)  in
                           (match uu____67052 with
                            | (arguments,result) ->
                                ((let uu____67281 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____67281
                                  then
                                    let uu____67284 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____67286 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____67289 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____67284 uu____67286 uu____67289
                                  else ());
                                 (let uu____67294 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____67294 with
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
                                      let uu____67312 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____67312 with
                                       | (result1,res_lcomp) ->
                                           let uu____67323 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____67323 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____67381 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____67381
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____67463  ->
                                                      fun uu____67464  ->
                                                        match (uu____67463,
                                                                uu____67464)
                                                        with
                                                        | ((bv,uu____67494),
                                                           (t2,uu____67496))
                                                            ->
                                                            let uu____67523 =
                                                              let uu____67524
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____67524.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____67523
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____67528 ->
                                                                 let uu____67529
                                                                   =
                                                                   let uu____67535
                                                                    =
                                                                    let uu____67537
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____67539
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____67537
                                                                    uu____67539
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____67535)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____67529
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____67544 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____67544
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____67546 =
                                                     let uu____67547 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____67547.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____67546 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____67550 -> ()
                                                   | uu____67551 ->
                                                       let uu____67552 =
                                                         let uu____67558 =
                                                           let uu____67560 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____67562 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____67560
                                                             uu____67562
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____67558)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____67552
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____67567 =
                                                       let uu____67568 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____67568.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____67567 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____67572;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____67573;_},tuvs)
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
                                                                    let uu____67587
                                                                    =
                                                                    let uu____67588
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____67589
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
                                                                    uu____67588
                                                                    uu____67589
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67587)
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
                                                     | uu____67595 ->
                                                         let uu____67596 =
                                                           let uu____67602 =
                                                             let uu____67604
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____67606
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____67604
                                                               uu____67606
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____67602)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____67596
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____67624  ->
                                                            fun u_x  ->
                                                              match uu____67624
                                                              with
                                                              | (x,uu____67633)
                                                                  ->
                                                                  let uu____67638
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67638)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____67642 =
                                                       let uu____67651 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____67691 
                                                                 ->
                                                                 match uu____67691
                                                                 with
                                                                 | (x,uu____67705)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____67651
                                                         arguments1
                                                        in
                                                     let uu____67719 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____67642
                                                       uu____67719
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_67724 = se
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
                                                         (uu___768_67724.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_67724.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_67724.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_67724.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____67728 -> failwith "impossible"
  
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
            let uu___776_67795 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_67795.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_67795.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_67795.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____67805 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____67805
           then
             let uu____67810 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____67810
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____67853  ->
                     match uu____67853 with
                     | (se,uu____67859) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____67860,uu____67861,tps,k,uu____67864,uu____67865)
                              ->
                              let uu____67874 =
                                let uu____67875 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____67875
                                 in
                              FStar_Syntax_Syntax.null_binder uu____67874
                          | uu____67880 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____67909,uu____67910,t,uu____67912,uu____67913,uu____67914)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____67921 -> failwith "Impossible"))
              in
           let t =
             let uu____67926 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____67926
              in
           (let uu____67936 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____67936
            then
              let uu____67941 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____67941
            else ());
           (let uu____67946 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____67946 with
            | (uvs,t1) ->
                ((let uu____67966 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____67966
                  then
                    let uu____67971 =
                      let uu____67973 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____67973
                        (FStar_String.concat ", ")
                       in
                    let uu____67990 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____67971 uu____67990
                  else ());
                 (let uu____67995 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____67995 with
                  | (uvs1,t2) ->
                      let uu____68010 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____68010 with
                       | (args,uu____68034) ->
                           let uu____68055 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____68055 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____68160  ->
                                       fun uu____68161  ->
                                         match (uu____68160, uu____68161)
                                         with
                                         | ((x,uu____68183),(se,uu____68185))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____68201,tps,uu____68203,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____68215 =
                                                    let uu____68220 =
                                                      let uu____68221 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____68221.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____68220 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____68250 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____68250
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____68328
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____68347 -> ([], ty)
                                                     in
                                                  (match uu____68215 with
                                                   | (tps1,t3) ->
                                                       let uu___853_68356 =
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
                                                           (uu___853_68356.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_68356.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_68356.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_68356.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____68361 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____68368 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _68372  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _68372))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_68391  ->
                                                match uu___585_68391 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____68397,uu____68398,uu____68399,uu____68400,uu____68401);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____68402;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____68403;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____68404;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____68405;_}
                                                    -> (tc, uvs_universes)
                                                | uu____68418 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____68442  ->
                                           fun d  ->
                                             match uu____68442 with
                                             | (t3,uu____68451) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____68457,uu____68458,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____68469 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____68469
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_68470 = d
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
                                                          (uu___889_68470.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_68470.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_68470.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_68470.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____68474 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____68493 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____68493
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____68515 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____68515
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____68532 =
      let uu____68533 = FStar_Syntax_Subst.compress t  in
      uu____68533.FStar_Syntax_Syntax.n  in
    match uu____68532 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____68552 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____68558 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____68615 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____68684  ->
               match uu____68684 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____68728 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____68728  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____68615
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____68983 =
             let uu____68985 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____68985
              in
           debug_log env uu____68983);
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
           (let uu____68990 =
              let uu____68992 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____68992
               in
            debug_log env uu____68990);
           (let uu____68997 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____68997) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____69010 =
                  let uu____69011 = FStar_Syntax_Subst.compress btype1  in
                  uu____69011.FStar_Syntax_Syntax.n  in
                match uu____69010 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____69041 = try_get_fv t  in
                    (match uu____69041 with
                     | (fv,us) ->
                         let uu____69049 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____69049
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____69065  ->
                                 match uu____69065 with
                                 | (t1,uu____69074) ->
                                     let uu____69079 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____69079) args)
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
                          let uu____69134 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____69134
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____69138 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____69138
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
                            (fun uu____69165  ->
                               match uu____69165 with
                               | (b,uu____69174) ->
                                   let uu____69179 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____69179) sbs)
                           &&
                           ((let uu____69185 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____69185 with
                             | (uu____69191,return_type) ->
                                 let uu____69193 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____69193)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____69214 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____69218 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____69223) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____69251) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____69278,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____69337  ->
                          match uu____69337 with
                          | (p,uu____69350,t) ->
                              let bs =
                                let uu____69369 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____69369
                                 in
                              let uu____69378 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____69378 with
                               | (bs1,t1) ->
                                   let uu____69386 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____69386)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____69408,uu____69409)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____69472 ->
                    ((let uu____69474 =
                        let uu____69476 =
                          let uu____69478 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____69480 =
                            let uu____69482 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____69482  in
                          Prims.op_Hat uu____69478 uu____69480  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____69476
                         in
                      debug_log env uu____69474);
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
              (let uu____69505 =
                 let uu____69507 =
                   let uu____69509 =
                     let uu____69511 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____69511  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____69509  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____69507
                  in
               debug_log env uu____69505);
              (let uu____69515 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____69515 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____69534 =
                       let uu____69536 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____69536
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____69534
                      then
                        ((let uu____69540 =
                            let uu____69542 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____69542
                             in
                          debug_log env uu____69540);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____69553 =
                        already_unfolded ilid args unfolded env  in
                      if uu____69553
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____69584 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____69584  in
                         (let uu____69590 =
                            let uu____69592 =
                              let uu____69594 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____69594
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____69592
                             in
                          debug_log env uu____69590);
                         (let uu____69599 =
                            let uu____69600 = FStar_ST.op_Bang unfolded  in
                            let uu____69646 =
                              let uu____69653 =
                                let uu____69658 =
                                  let uu____69659 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____69659  in
                                (ilid, uu____69658)  in
                              [uu____69653]  in
                            FStar_List.append uu____69600 uu____69646  in
                          FStar_ST.op_Colon_Equals unfolded uu____69599);
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
                  (let uu____69808 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____69808 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____69831 ->
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
                         (let uu____69835 =
                            let uu____69837 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____69837
                             in
                          debug_log env uu____69835);
                         (let uu____69840 =
                            let uu____69841 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____69841.FStar_Syntax_Syntax.n  in
                          match uu____69840 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____69869 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____69869 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____69933 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____69933 dbs1
                                       in
                                    let c1 =
                                      let uu____69937 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____69937 c
                                       in
                                    let uu____69940 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____69940 with
                                     | (args1,uu____69975) ->
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
                                           let uu____70067 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____70067 c1
                                            in
                                         ((let uu____70077 =
                                             let uu____70079 =
                                               let uu____70081 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____70084 =
                                                 let uu____70086 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____70086
                                                  in
                                               Prims.op_Hat uu____70081
                                                 uu____70084
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____70079
                                              in
                                           debug_log env uu____70077);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____70120 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____70123 =
                                  let uu____70124 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____70124.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____70123
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
                   (let uu____70193 = try_get_fv t1  in
                    match uu____70193 with
                    | (fv,uu____70200) ->
                        let uu____70201 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____70201
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____70233 =
                      let uu____70235 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____70235
                       in
                    debug_log env uu____70233);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____70240 =
                      FStar_List.fold_left
                        (fun uu____70261  ->
                           fun b  ->
                             match uu____70261 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____70292 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____70316 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____70292, uu____70316))) (true, env)
                        sbs1
                       in
                    match uu____70240 with | (b,uu____70334) -> b))
              | uu____70337 ->
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
              let uu____70393 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____70393 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____70416 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____70419 =
                      let uu____70421 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____70421
                       in
                    debug_log env uu____70419);
                   (let uu____70424 =
                      let uu____70425 = FStar_Syntax_Subst.compress dt  in
                      uu____70425.FStar_Syntax_Syntax.n  in
                    match uu____70424 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____70429 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____70434) ->
                        let dbs1 =
                          let uu____70464 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____70464  in
                        let dbs2 =
                          let uu____70514 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____70514 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____70519 =
                            let uu____70521 =
                              let uu____70523 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____70523 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____70521
                             in
                          debug_log env uu____70519);
                         (let uu____70533 =
                            FStar_List.fold_left
                              (fun uu____70554  ->
                                 fun b  ->
                                   match uu____70554 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____70585 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____70609 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____70585, uu____70609)))
                              (true, env) dbs3
                             in
                          match uu____70533 with | (b,uu____70627) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____70630,uu____70631) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____70687 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____70710 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____70726,uu____70727,uu____70728) -> (lid, us, bs)
        | uu____70737 -> failwith "Impossible!"  in
      match uu____70710 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____70749 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____70749 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____70773 =
                 let uu____70776 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____70776  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____70790 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____70790
                      unfolded_inductives env2) uu____70773)
  
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
        (uu____70869,uu____70870,t,uu____70872,uu____70873,uu____70874) -> t
    | uu____70881 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____70908 =
         let uu____70910 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____70910 haseq_suffix  in
       uu____70908 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____70934 =
      let uu____70937 =
        let uu____70940 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____70940]  in
      FStar_List.append lid.FStar_Ident.ns uu____70937  in
    FStar_Ident.lid_of_ids uu____70934
  
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
          let uu____70986 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____71000,bs,t,uu____71003,uu____71004) ->
                (lid, bs, t)
            | uu____71013 -> failwith "Impossible!"  in
          match uu____70986 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____71036 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____71036 t  in
              let uu____71045 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____71045 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____71063 =
                       let uu____71064 = FStar_Syntax_Subst.compress t2  in
                       uu____71064.FStar_Syntax_Syntax.n  in
                     match uu____71063 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____71068) -> ibs
                     | uu____71089 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____71098 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____71099 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____71098 uu____71099
                      in
                   let ind1 =
                     let uu____71105 =
                       let uu____71110 =
                         FStar_List.map
                           (fun uu____71127  ->
                              match uu____71127 with
                              | (bv,aq) ->
                                  let uu____71146 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71146, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____71110  in
                     uu____71105 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____71154 =
                       let uu____71159 =
                         FStar_List.map
                           (fun uu____71176  ->
                              match uu____71176 with
                              | (bv,aq) ->
                                  let uu____71195 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71195, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____71159  in
                     uu____71154 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____71203 =
                       let uu____71208 =
                         let uu____71209 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____71209]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____71208
                        in
                     uu____71203 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____71260 =
                            let uu____71261 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____71261  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____71260) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____71274 =
                              let uu____71277 =
                                let uu____71282 =
                                  let uu____71283 =
                                    let uu____71292 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____71292
                                     in
                                  [uu____71283]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____71282
                                 in
                              uu____71277 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____71274)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_71317 = fml  in
                     let uu____71318 =
                       let uu____71319 =
                         let uu____71326 =
                           let uu____71327 =
                             let uu____71340 =
                               let uu____71351 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____71351]  in
                             [uu____71340]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____71327  in
                         (fml, uu____71326)  in
                       FStar_Syntax_Syntax.Tm_meta uu____71319  in
                     {
                       FStar_Syntax_Syntax.n = uu____71318;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_71317.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_71317.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71406 =
                              let uu____71411 =
                                let uu____71412 =
                                  let uu____71421 =
                                    let uu____71422 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71422
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71421  in
                                [uu____71412]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71411
                               in
                            uu____71406 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71479 =
                              let uu____71484 =
                                let uu____71485 =
                                  let uu____71494 =
                                    let uu____71495 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71495
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71494  in
                                [uu____71485]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71484
                               in
                            uu____71479 FStar_Pervasives_Native.None
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
          let uu____71572 =
            let uu____71573 = FStar_Syntax_Subst.compress dt1  in
            uu____71573.FStar_Syntax_Syntax.n  in
          match uu____71572 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____71577) ->
              let dbs1 =
                let uu____71607 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____71607  in
              let dbs2 =
                let uu____71657 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____71657 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____71672 =
                           let uu____71677 =
                             let uu____71678 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____71678]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____71677
                            in
                         uu____71672 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____71711 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____71711 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____71721 =
                       let uu____71726 =
                         let uu____71727 =
                           let uu____71736 =
                             let uu____71737 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____71737
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____71736  in
                         [uu____71727]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____71726
                        in
                     uu____71721 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____71786 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____71877,uu____71878,uu____71879,uu____71880,uu____71881)
                  -> lid
              | uu____71890 -> failwith "Impossible!"  in
            let uu____71892 = acc  in
            match uu____71892 with
            | (uu____71929,en,uu____71931,uu____71932) ->
                let uu____71953 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____71953 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____71990 = acc  in
                     (match uu____71990 with
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
                                     (uu____72065,uu____72066,uu____72067,t_lid,uu____72069,uu____72070)
                                     -> t_lid = lid
                                 | uu____72077 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____72092 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____72092)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____72095 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____72098 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____72095, uu____72098)))
  
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
          let uu____72156 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____72166,us,uu____72168,t,uu____72170,uu____72171) ->
                (us, t)
            | uu____72180 -> failwith "Impossible!"  in
          match uu____72156 with
          | (us,t) ->
              let uu____72190 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____72190 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____72216 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____72216 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____72294 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____72294 with
                           | (uu____72309,t1) ->
                               let uu____72331 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____72331
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____72336 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____72336 with
                          | (phi1,uu____72344) ->
                              ((let uu____72346 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____72346
                                then
                                  let uu____72349 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____72349
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____72367  ->
                                         match uu____72367 with
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
                let uu____72439 =
                  let uu____72440 = FStar_Syntax_Subst.compress t  in
                  uu____72440.FStar_Syntax_Syntax.n  in
                match uu____72439 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____72448) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____72485 = is_mutual t'  in
                    if uu____72485
                    then true
                    else
                      (let uu____72492 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____72492)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____72512) ->
                    is_mutual t'
                | uu____72517 -> false
              
              and exists_mutual uu___586_72519 =
                match uu___586_72519 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____72540 =
                let uu____72541 = FStar_Syntax_Subst.compress dt1  in
                uu____72541.FStar_Syntax_Syntax.n  in
              match uu____72540 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____72547) ->
                  let dbs1 =
                    let uu____72577 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____72577  in
                  let dbs2 =
                    let uu____72627 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____72627 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____72647 =
                               let uu____72652 =
                                 let uu____72653 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____72653]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____72652
                                in
                             uu____72647 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____72685 = is_mutual sort  in
                             if uu____72685
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
                           let uu____72700 =
                             let uu____72705 =
                               let uu____72706 =
                                 let uu____72715 =
                                   let uu____72716 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____72716 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____72715  in
                               [uu____72706]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____72705
                              in
                           uu____72700 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____72765 -> acc
  
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
              let uu____72815 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____72837,bs,t,uu____72840,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____72852 -> failwith "Impossible!"  in
              match uu____72815 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____72876 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____72876 t  in
                  let uu____72885 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____72885 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____72895 =
                           let uu____72896 = FStar_Syntax_Subst.compress t2
                              in
                           uu____72896.FStar_Syntax_Syntax.n  in
                         match uu____72895 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____72900) ->
                             ibs
                         | uu____72921 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____72930 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____72931 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____72930
                           uu____72931
                          in
                       let ind1 =
                         let uu____72937 =
                           let uu____72942 =
                             FStar_List.map
                               (fun uu____72959  ->
                                  match uu____72959 with
                                  | (bv,aq) ->
                                      let uu____72978 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72978, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____72942  in
                         uu____72937 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____72986 =
                           let uu____72991 =
                             FStar_List.map
                               (fun uu____73008  ->
                                  match uu____73008 with
                                  | (bv,aq) ->
                                      let uu____73027 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____73027, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____72991  in
                         uu____72986 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____73035 =
                           let uu____73040 =
                             let uu____73041 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____73041]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____73040
                            in
                         uu____73035 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____73080,uu____73081,uu____73082,t_lid,uu____73084,uu____73085)
                                  -> t_lid = lid
                              | uu____73092 -> failwith "Impossible")
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
                         let uu___1460_73104 = fml  in
                         let uu____73105 =
                           let uu____73106 =
                             let uu____73113 =
                               let uu____73114 =
                                 let uu____73127 =
                                   let uu____73138 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____73138]  in
                                 [uu____73127]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____73114
                                in
                             (fml, uu____73113)  in
                           FStar_Syntax_Syntax.Tm_meta uu____73106  in
                         {
                           FStar_Syntax_Syntax.n = uu____73105;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_73104.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_73104.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73193 =
                                  let uu____73198 =
                                    let uu____73199 =
                                      let uu____73208 =
                                        let uu____73209 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73209
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73208
                                       in
                                    [uu____73199]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73198
                                   in
                                uu____73193 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73266 =
                                  let uu____73271 =
                                    let uu____73272 =
                                      let uu____73281 =
                                        let uu____73282 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73282
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73281
                                       in
                                    [uu____73272]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73271
                                   in
                                uu____73266 FStar_Pervasives_Native.None
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
                     (lid,uu____73376,uu____73377,uu____73378,uu____73379,uu____73380)
                     -> lid
                 | uu____73389 -> failwith "Impossible!") tcs
             in
          let uu____73391 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____73403,uu____73404,uu____73405,uu____73406) ->
                (lid, us)
            | uu____73415 -> failwith "Impossible!"  in
          match uu____73391 with
          | (lid,us) ->
              let uu____73425 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____73425 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____73452 =
                       let uu____73453 =
                         let uu____73460 = get_haseq_axiom_lid lid  in
                         (uu____73460, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____73453  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____73452;
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
          let uu____73514 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_73539  ->
                    match uu___587_73539 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____73541;
                        FStar_Syntax_Syntax.sigrng = uu____73542;
                        FStar_Syntax_Syntax.sigquals = uu____73543;
                        FStar_Syntax_Syntax.sigmeta = uu____73544;
                        FStar_Syntax_Syntax.sigattrs = uu____73545;_} -> true
                    | uu____73567 -> false))
             in
          match uu____73514 with
          | (tys,datas) ->
              ((let uu____73590 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_73601  ->
                          match uu___588_73601 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____73603;
                              FStar_Syntax_Syntax.sigrng = uu____73604;
                              FStar_Syntax_Syntax.sigquals = uu____73605;
                              FStar_Syntax_Syntax.sigmeta = uu____73606;
                              FStar_Syntax_Syntax.sigattrs = uu____73607;_}
                              -> false
                          | uu____73628 -> true))
                   in
                if uu____73590
                then
                  let uu____73631 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____73631
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____73646 =
                       let uu____73647 = FStar_List.hd tys  in
                       uu____73647.FStar_Syntax_Syntax.sigel  in
                     match uu____73646 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____73650,uvs,uu____73652,uu____73653,uu____73654,uu____73655)
                         -> uvs
                     | uu____73664 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____73669 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____73699 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____73699 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____73737,bs,t,l1,l2) ->
                                      let uu____73750 =
                                        let uu____73767 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____73768 =
                                          let uu____73769 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____73769 t
                                           in
                                        (lid, univs2, uu____73767,
                                          uu____73768, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____73750
                                  | uu____73782 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_73784 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_73784.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_73784.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_73784.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_73784.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____73794,t,lid_t,x,l) ->
                                      let uu____73805 =
                                        let uu____73821 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____73821, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____73805
                                  | uu____73825 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_73827 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_73827.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_73827.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_73827.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_73827.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____73828 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____73828, tys1, datas1))
                   in
                match uu____73669 with
                | (env1,tys1,datas1) ->
                    let uu____73854 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____73893  ->
                             match uu____73893 with
                             | (env2,all_tcs,g) ->
                                 let uu____73933 = tc_tycon env2 tc  in
                                 (match uu____73933 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____73960 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____73960
                                        then
                                          let uu____73963 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____73963
                                        else ());
                                       (let uu____73968 =
                                          let uu____73969 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____73969
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____73968))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____73854 with
                     | (env2,tcs,g) ->
                         let uu____74015 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____74037  ->
                                  match uu____74037 with
                                  | (datas2,g1) ->
                                      let uu____74056 =
                                        let uu____74061 = tc_data env2 tcs
                                           in
                                        uu____74061 se  in
                                      (match uu____74056 with
                                       | (data,g') ->
                                           let uu____74078 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____74078)))
                             datas1 ([], g)
                            in
                         (match uu____74015 with
                          | (datas2,g1) ->
                              let uu____74099 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____74121 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____74121, datas2))
                                 in
                              (match uu____74099 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____74153 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____74154 =
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
                                         uu____74153;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____74154
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____74180,uu____74181)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____74201 =
                                                    let uu____74207 =
                                                      let uu____74209 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____74211 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____74209
                                                        uu____74211
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____74207)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____74201
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____74215 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____74215 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____74231)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____74262 ->
                                                             let uu____74263
                                                               =
                                                               let uu____74270
                                                                 =
                                                                 let uu____74271
                                                                   =
                                                                   let uu____74286
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____74286)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____74271
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____74270
                                                                in
                                                             uu____74263
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
                                                       let uu____74311 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____74311
                                                        with
                                                        | (uu____74316,inferred)
                                                            ->
                                                            let uu____74318 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____74318
                                                             with
                                                             | (uu____74323,expected)
                                                                 ->
                                                                 let uu____74325
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____74325
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____74332 -> ()));
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
                          let uu____74443 =
                            let uu____74450 =
                              let uu____74451 =
                                let uu____74458 =
                                  let uu____74461 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____74461
                                   in
                                (uu____74458, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____74451  in
                            FStar_Syntax_Syntax.mk uu____74450  in
                          uu____74443 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____74498  ->
                                  match uu____74498 with
                                  | (x,imp) ->
                                      let uu____74517 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____74517, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____74521 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____74521  in
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
                               let uu____74544 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____74544
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____74546 =
                               let uu____74549 =
                                 let uu____74552 =
                                   let uu____74557 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____74558 =
                                     let uu____74559 =
                                       let uu____74568 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____74568
                                        in
                                     [uu____74559]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____74557
                                     uu____74558
                                    in
                                 uu____74552 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____74549  in
                             FStar_Syntax_Util.refine x uu____74546  in
                           let uu____74595 =
                             let uu___1671_74596 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_74596.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_74596.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____74595)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____74613 =
                          FStar_List.map
                            (fun uu____74637  ->
                               match uu____74637 with
                               | (x,uu____74651) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____74613 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____74710  ->
                                match uu____74710 with
                                | (x,uu____74724) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____74735 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____74735)
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
                               (let uu____74756 =
                                  let uu____74758 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____74758.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____74756)
                              in
                           let quals =
                             let uu____74762 =
                               FStar_List.filter
                                 (fun uu___589_74766  ->
                                    match uu___589_74766 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____74771 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____74762
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____74809 =
                                 let uu____74810 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____74810  in
                               FStar_Syntax_Syntax.mk_Total uu____74809  in
                             let uu____74811 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____74811
                              in
                           let decl =
                             let uu____74815 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____74815;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____74817 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____74817
                            then
                              let uu____74821 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____74821
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
                                             fun uu____74882  ->
                                               match uu____74882 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____74911 =
                                                       let uu____74914 =
                                                         let uu____74915 =
                                                           let uu____74922 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____74922,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____74915
                                                          in
                                                       pos uu____74914  in
                                                     (uu____74911, b)
                                                   else
                                                     (let uu____74930 =
                                                        let uu____74933 =
                                                          let uu____74934 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____74934
                                                           in
                                                        pos uu____74933  in
                                                      (uu____74930, b))))
                                      in
                                   let pat_true =
                                     let uu____74953 =
                                       let uu____74956 =
                                         let uu____74957 =
                                           let uu____74971 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____74971, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____74957
                                          in
                                       pos uu____74956  in
                                     (uu____74953,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____75006 =
                                       let uu____75009 =
                                         let uu____75010 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____75010
                                          in
                                       pos uu____75009  in
                                     (uu____75006,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____75024 =
                                     let uu____75031 =
                                       let uu____75032 =
                                         let uu____75055 =
                                           let uu____75072 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____75087 =
                                             let uu____75104 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____75104]  in
                                           uu____75072 :: uu____75087  in
                                         (arg_exp, uu____75055)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____75032
                                        in
                                     FStar_Syntax_Syntax.mk uu____75031  in
                                   uu____75024 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____75183 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____75183
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
                                let uu____75205 =
                                  let uu____75210 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____75210  in
                                let uu____75211 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____75205
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____75211 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____75217 =
                                  let uu____75218 =
                                    let uu____75225 =
                                      let uu____75228 =
                                        let uu____75229 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____75229
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____75228]  in
                                    ((false, [lb]), uu____75225)  in
                                  FStar_Syntax_Syntax.Sig_let uu____75218  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____75217;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____75243 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____75243
                               then
                                 let uu____75247 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____75247
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
                                fun uu____75320  ->
                                  match uu____75320 with
                                  | (a,uu____75329) ->
                                      let uu____75334 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____75334 with
                                       | (field_name,uu____75340) ->
                                           let field_proj_tm =
                                             let uu____75342 =
                                               let uu____75343 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____75343
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____75342 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____75369 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____75411  ->
                                    match uu____75411 with
                                    | (x,uu____75422) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____75428 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____75428 with
                                         | (field_name,uu____75436) ->
                                             let t =
                                               let uu____75440 =
                                                 let uu____75441 =
                                                   let uu____75444 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____75444
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____75441
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____75440
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____75450 =
                                                    let uu____75452 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____75452.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____75450)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____75471 =
                                                   FStar_List.filter
                                                     (fun uu___590_75475  ->
                                                        match uu___590_75475
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____75478 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____75471
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_75493  ->
                                                         match uu___591_75493
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____75499 ->
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
                                               let uu____75510 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____75510;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____75512 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____75512
                                               then
                                                 let uu____75516 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____75516
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
                                                           fun uu____75570 
                                                             ->
                                                             match uu____75570
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
                                                                   let uu____75600
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____75600,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____75620
                                                                    =
                                                                    let uu____75623
                                                                    =
                                                                    let uu____75624
                                                                    =
                                                                    let uu____75631
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____75631,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____75624
                                                                     in
                                                                    pos
                                                                    uu____75623
                                                                     in
                                                                    (uu____75620,
                                                                    b))
                                                                   else
                                                                    (let uu____75639
                                                                    =
                                                                    let uu____75642
                                                                    =
                                                                    let uu____75643
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____75643
                                                                     in
                                                                    pos
                                                                    uu____75642
                                                                     in
                                                                    (uu____75639,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____75662 =
                                                     let uu____75665 =
                                                       let uu____75666 =
                                                         let uu____75680 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____75680,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____75666
                                                        in
                                                     pos uu____75665  in
                                                   let uu____75690 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____75662,
                                                     FStar_Pervasives_Native.None,
                                                     uu____75690)
                                                    in
                                                 let body =
                                                   let uu____75706 =
                                                     let uu____75713 =
                                                       let uu____75714 =
                                                         let uu____75737 =
                                                           let uu____75754 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____75754]  in
                                                         (arg_exp,
                                                           uu____75737)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____75714
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____75713
                                                      in
                                                   uu____75706
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____75822 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____75822
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
                                                   let uu____75841 =
                                                     let uu____75846 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____75846
                                                      in
                                                   let uu____75847 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____75841;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____75847;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____75853 =
                                                     let uu____75854 =
                                                       let uu____75861 =
                                                         let uu____75864 =
                                                           let uu____75865 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____75865
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____75864]  in
                                                       ((false, [lb]),
                                                         uu____75861)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____75854
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____75853;
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
                                                 (let uu____75879 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____75879
                                                  then
                                                    let uu____75883 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____75883
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____75369 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____75937) when
              let uu____75944 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____75944 ->
              let uu____75946 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____75946 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____75968 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____75968 with
                    | (formals,uu____75986) ->
                        let uu____76007 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____76042 =
                                   let uu____76044 =
                                     let uu____76045 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____76045  in
                                   FStar_Ident.lid_equals typ_lid uu____76044
                                    in
                                 if uu____76042
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____76067,uvs',tps,typ0,uu____76071,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____76091 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____76140 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____76140
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____76007 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____76178 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____76178 with
                              | (indices,uu____76196) ->
                                  let refine_domain =
                                    let uu____76219 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_76226  ->
                                              match uu___592_76226 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____76228 -> true
                                              | uu____76238 -> false))
                                       in
                                    if uu____76219
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_76253 =
                                      match uu___593_76253 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____76256,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____76268 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____76269 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____76269 with
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
                                    let uu____76282 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____76282 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____76365  ->
                                               fun uu____76366  ->
                                                 match (uu____76365,
                                                         uu____76366)
                                                 with
                                                 | ((x,uu____76392),(x',uu____76394))
                                                     ->
                                                     let uu____76415 =
                                                       let uu____76422 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____76422)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____76415) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____76427 -> []
  