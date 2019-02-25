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
          let uu____66206 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____66206 with
           | (usubst,uvs1) ->
               let uu____66233 =
                 let uu____66240 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____66241 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____66242 =
                   let uu____66243 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____66243 k  in
                 (uu____66240, uu____66241, uu____66242)  in
               (match uu____66233 with
                | (env1,tps1,k1) ->
                    let uu____66263 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____66263 with
                     | (tps2,k2) ->
                         let uu____66278 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____66278 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____66299 =
                                let uu____66318 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____66318 with
                                | (k3,uu____66344,g) ->
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
                                    let uu____66347 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____66362 =
                                      let uu____66363 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____66363
                                       in
                                    (uu____66347, uu____66362)
                                 in
                              (match uu____66299 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____66426 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____66426
                                      in
                                   let uu____66429 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____66429 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____66447 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____66447))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____66454 =
                                              let uu____66460 =
                                                let uu____66462 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____66464 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____66462 uu____66464
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____66460)
                                               in
                                            FStar_Errors.raise_error
                                              uu____66454
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
                                            let uu____66477 =
                                              let uu____66486 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____66503 =
                                                let uu____66512 =
                                                  let uu____66525 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____66525
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____66512
                                                 in
                                              FStar_List.append uu____66486
                                                uu____66503
                                               in
                                            let uu____66548 =
                                              let uu____66551 =
                                                let uu____66552 =
                                                  let uu____66557 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____66557
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____66552
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____66551
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____66477 uu____66548
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____66574 =
                                            let uu____66579 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____66580 =
                                              let uu____66581 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____66581 k4
                                               in
                                            (uu____66579, uu____66580)  in
                                          match uu____66574 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____66601 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____66601,
                                                (let uu___646_66607 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_66607.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_66607.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_66607.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_66607.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____66612 -> failwith "impossible"
  
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
            let uu____66676 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____66676 with
             | (usubst,_uvs1) ->
                 let uu____66699 =
                   let uu____66704 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____66705 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____66704, uu____66705)  in
                 (match uu____66699 with
                  | (env1,t1) ->
                      let uu____66712 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____66751  ->
                               match uu____66751 with
                               | (se1,u_tc) ->
                                   let uu____66766 =
                                     let uu____66768 =
                                       let uu____66769 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____66769  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____66768
                                      in
                                   if uu____66766
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____66789,uu____66790,tps,uu____66792,uu____66793,uu____66794)
                                          ->
                                          let tps1 =
                                            let uu____66804 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____66804
                                              (FStar_List.map
                                                 (fun uu____66844  ->
                                                    match uu____66844 with
                                                    | (x,uu____66858) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____66866 =
                                            let uu____66873 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____66873, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____66866
                                      | uu____66880 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____66923 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____66923
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____66712 with
                       | (env2,tps,u_tc) ->
                           let uu____66955 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____66971 =
                               let uu____66972 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____66972.FStar_Syntax_Syntax.n  in
                             match uu____66971 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____67011 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____67011 with
                                  | (uu____67052,bs') ->
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
                                                fun uu____67123  ->
                                                  match uu____67123 with
                                                  | (x,uu____67132) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____67139 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____67139)
                             | uu____67140 -> ([], t2)  in
                           (match uu____66955 with
                            | (arguments,result) ->
                                ((let uu____67184 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____67184
                                  then
                                    let uu____67187 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____67189 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____67192 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____67187 uu____67189 uu____67192
                                  else ());
                                 (let uu____67197 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____67197 with
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
                                      let uu____67215 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____67215 with
                                       | (result1,res_lcomp) ->
                                           let uu____67226 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____67226 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____67284 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____67284
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____67366  ->
                                                      fun uu____67367  ->
                                                        match (uu____67366,
                                                                uu____67367)
                                                        with
                                                        | ((bv,uu____67397),
                                                           (t2,uu____67399))
                                                            ->
                                                            let uu____67426 =
                                                              let uu____67427
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____67427.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____67426
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____67431 ->
                                                                 let uu____67432
                                                                   =
                                                                   let uu____67438
                                                                    =
                                                                    let uu____67440
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____67442
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____67440
                                                                    uu____67442
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____67438)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____67432
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____67447 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____67447
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____67449 =
                                                     let uu____67450 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____67450.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____67449 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____67453 -> ()
                                                   | uu____67454 ->
                                                       let uu____67455 =
                                                         let uu____67461 =
                                                           let uu____67463 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____67465 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____67463
                                                             uu____67465
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____67461)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____67455
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____67470 =
                                                       let uu____67471 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____67471.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____67470 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____67475;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____67476;_},tuvs)
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
                                                                    let uu____67490
                                                                    =
                                                                    let uu____67491
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____67492
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
                                                                    uu____67491
                                                                    uu____67492
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67490)
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
                                                     | uu____67498 ->
                                                         let uu____67499 =
                                                           let uu____67505 =
                                                             let uu____67507
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____67509
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____67507
                                                               uu____67509
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____67505)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____67499
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____67527  ->
                                                            fun u_x  ->
                                                              match uu____67527
                                                              with
                                                              | (x,uu____67536)
                                                                  ->
                                                                  let uu____67541
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67541)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____67545 =
                                                       let uu____67554 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____67594 
                                                                 ->
                                                                 match uu____67594
                                                                 with
                                                                 | (x,uu____67608)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____67554
                                                         arguments1
                                                        in
                                                     let uu____67622 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____67545
                                                       uu____67622
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_67627 = se
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
                                                         (uu___768_67627.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_67627.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_67627.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_67627.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____67631 -> failwith "impossible"
  
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
            let uu___776_67698 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_67698.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_67698.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_67698.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____67708 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____67708
           then
             let uu____67713 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____67713
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____67756  ->
                     match uu____67756 with
                     | (se,uu____67762) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____67763,uu____67764,tps,k,uu____67767,uu____67768)
                              ->
                              let uu____67777 =
                                let uu____67778 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____67778
                                 in
                              FStar_Syntax_Syntax.null_binder uu____67777
                          | uu____67783 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____67812,uu____67813,t,uu____67815,uu____67816,uu____67817)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____67824 -> failwith "Impossible"))
              in
           let t =
             let uu____67829 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____67829
              in
           (let uu____67839 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____67839
            then
              let uu____67844 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____67844
            else ());
           (let uu____67849 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____67849 with
            | (uvs,t1) ->
                ((let uu____67869 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____67869
                  then
                    let uu____67874 =
                      let uu____67876 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____67876
                        (FStar_String.concat ", ")
                       in
                    let uu____67893 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____67874 uu____67893
                  else ());
                 (let uu____67898 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____67898 with
                  | (uvs1,t2) ->
                      let uu____67913 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____67913 with
                       | (args,uu____67937) ->
                           let uu____67958 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____67958 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____68063  ->
                                       fun uu____68064  ->
                                         match (uu____68063, uu____68064)
                                         with
                                         | ((x,uu____68086),(se,uu____68088))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____68104,tps,uu____68106,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____68118 =
                                                    let uu____68123 =
                                                      let uu____68124 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____68124.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____68123 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____68153 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____68153
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____68231
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____68250 -> ([], ty)
                                                     in
                                                  (match uu____68118 with
                                                   | (tps1,t3) ->
                                                       let uu___853_68259 =
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
                                                           (uu___853_68259.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_68259.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_68259.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_68259.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____68264 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____68271 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _68275  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _68275))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_68294  ->
                                                match uu___585_68294 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____68300,uu____68301,uu____68302,uu____68303,uu____68304);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____68305;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____68306;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____68307;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____68308;_}
                                                    -> (tc, uvs_universes)
                                                | uu____68321 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____68345  ->
                                           fun d  ->
                                             match uu____68345 with
                                             | (t3,uu____68354) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____68360,uu____68361,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____68372 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____68372
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_68373 = d
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
                                                          (uu___889_68373.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_68373.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_68373.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_68373.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____68377 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____68396 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____68396
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____68418 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____68418
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____68435 =
      let uu____68436 = FStar_Syntax_Subst.compress t  in
      uu____68436.FStar_Syntax_Syntax.n  in
    match uu____68435 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____68455 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____68461 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____68518 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____68587  ->
               match uu____68587 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____68631 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____68631  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____68518
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____68886 =
             let uu____68888 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____68888
              in
           debug_log env uu____68886);
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
           (let uu____68893 =
              let uu____68895 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____68895
               in
            debug_log env uu____68893);
           (let uu____68900 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____68900) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____68913 =
                  let uu____68914 = FStar_Syntax_Subst.compress btype1  in
                  uu____68914.FStar_Syntax_Syntax.n  in
                match uu____68913 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____68944 = try_get_fv t  in
                    (match uu____68944 with
                     | (fv,us) ->
                         let uu____68952 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____68952
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____68968  ->
                                 match uu____68968 with
                                 | (t1,uu____68977) ->
                                     let uu____68982 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____68982) args)
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
                          let uu____69037 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____69037
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____69041 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____69041
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
                            (fun uu____69068  ->
                               match uu____69068 with
                               | (b,uu____69077) ->
                                   let uu____69082 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____69082) sbs)
                           &&
                           ((let uu____69088 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____69088 with
                             | (uu____69094,return_type) ->
                                 let uu____69096 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____69096)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____69117 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____69121 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____69126) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____69154) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____69181,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____69240  ->
                          match uu____69240 with
                          | (p,uu____69253,t) ->
                              let bs =
                                let uu____69272 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____69272
                                 in
                              let uu____69281 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____69281 with
                               | (bs1,t1) ->
                                   let uu____69289 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____69289)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____69311,uu____69312)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____69375 ->
                    ((let uu____69377 =
                        let uu____69379 =
                          let uu____69381 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____69383 =
                            let uu____69385 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____69385  in
                          Prims.op_Hat uu____69381 uu____69383  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____69379
                         in
                      debug_log env uu____69377);
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
              (let uu____69408 =
                 let uu____69410 =
                   let uu____69412 =
                     let uu____69414 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____69414  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____69412  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____69410
                  in
               debug_log env uu____69408);
              (let uu____69418 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____69418 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____69437 =
                       let uu____69439 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____69439
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____69437
                      then
                        ((let uu____69443 =
                            let uu____69445 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____69445
                             in
                          debug_log env uu____69443);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____69456 =
                        already_unfolded ilid args unfolded env  in
                      if uu____69456
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____69487 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____69487  in
                         (let uu____69493 =
                            let uu____69495 =
                              let uu____69497 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____69497
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____69495
                             in
                          debug_log env uu____69493);
                         (let uu____69502 =
                            let uu____69503 = FStar_ST.op_Bang unfolded  in
                            let uu____69549 =
                              let uu____69556 =
                                let uu____69561 =
                                  let uu____69562 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____69562  in
                                (ilid, uu____69561)  in
                              [uu____69556]  in
                            FStar_List.append uu____69503 uu____69549  in
                          FStar_ST.op_Colon_Equals unfolded uu____69502);
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
                  (let uu____69711 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____69711 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____69734 ->
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
                         (let uu____69738 =
                            let uu____69740 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____69740
                             in
                          debug_log env uu____69738);
                         (let uu____69743 =
                            let uu____69744 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____69744.FStar_Syntax_Syntax.n  in
                          match uu____69743 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____69772 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____69772 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____69836 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____69836 dbs1
                                       in
                                    let c1 =
                                      let uu____69840 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____69840 c
                                       in
                                    let uu____69843 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____69843 with
                                     | (args1,uu____69878) ->
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
                                           let uu____69970 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____69970 c1
                                            in
                                         ((let uu____69980 =
                                             let uu____69982 =
                                               let uu____69984 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____69987 =
                                                 let uu____69989 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____69989
                                                  in
                                               Prims.op_Hat uu____69984
                                                 uu____69987
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____69982
                                              in
                                           debug_log env uu____69980);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____70023 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____70026 =
                                  let uu____70027 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____70027.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____70026
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
                   (let uu____70096 = try_get_fv t1  in
                    match uu____70096 with
                    | (fv,uu____70103) ->
                        let uu____70104 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____70104
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____70136 =
                      let uu____70138 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____70138
                       in
                    debug_log env uu____70136);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____70143 =
                      FStar_List.fold_left
                        (fun uu____70164  ->
                           fun b  ->
                             match uu____70164 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____70195 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____70219 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____70195, uu____70219))) (true, env)
                        sbs1
                       in
                    match uu____70143 with | (b,uu____70237) -> b))
              | uu____70240 ->
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
              let uu____70296 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____70296 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____70319 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____70322 =
                      let uu____70324 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____70324
                       in
                    debug_log env uu____70322);
                   (let uu____70327 =
                      let uu____70328 = FStar_Syntax_Subst.compress dt  in
                      uu____70328.FStar_Syntax_Syntax.n  in
                    match uu____70327 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____70332 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____70337) ->
                        let dbs1 =
                          let uu____70367 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____70367  in
                        let dbs2 =
                          let uu____70417 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____70417 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____70422 =
                            let uu____70424 =
                              let uu____70426 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____70426 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____70424
                             in
                          debug_log env uu____70422);
                         (let uu____70436 =
                            FStar_List.fold_left
                              (fun uu____70457  ->
                                 fun b  ->
                                   match uu____70457 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____70488 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____70512 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____70488, uu____70512)))
                              (true, env) dbs3
                             in
                          match uu____70436 with | (b,uu____70530) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____70533,uu____70534) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____70590 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____70613 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____70629,uu____70630,uu____70631) -> (lid, us, bs)
        | uu____70640 -> failwith "Impossible!"  in
      match uu____70613 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____70652 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____70652 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____70676 =
                 let uu____70679 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____70679  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____70693 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____70693
                      unfolded_inductives env2) uu____70676)
  
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
        (uu____70772,uu____70773,t,uu____70775,uu____70776,uu____70777) -> t
    | uu____70784 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____70811 =
         let uu____70813 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____70813 haseq_suffix  in
       uu____70811 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____70837 =
      let uu____70840 =
        let uu____70843 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____70843]  in
      FStar_List.append lid.FStar_Ident.ns uu____70840  in
    FStar_Ident.lid_of_ids uu____70837
  
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
          let uu____70889 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____70903,bs,t,uu____70906,uu____70907) ->
                (lid, bs, t)
            | uu____70916 -> failwith "Impossible!"  in
          match uu____70889 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____70939 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____70939 t  in
              let uu____70948 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____70948 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____70966 =
                       let uu____70967 = FStar_Syntax_Subst.compress t2  in
                       uu____70967.FStar_Syntax_Syntax.n  in
                     match uu____70966 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____70971) -> ibs
                     | uu____70992 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____71001 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____71002 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____71001 uu____71002
                      in
                   let ind1 =
                     let uu____71008 =
                       let uu____71013 =
                         FStar_List.map
                           (fun uu____71030  ->
                              match uu____71030 with
                              | (bv,aq) ->
                                  let uu____71049 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71049, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____71013  in
                     uu____71008 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____71057 =
                       let uu____71062 =
                         FStar_List.map
                           (fun uu____71079  ->
                              match uu____71079 with
                              | (bv,aq) ->
                                  let uu____71098 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71098, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____71062  in
                     uu____71057 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____71106 =
                       let uu____71111 =
                         let uu____71112 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____71112]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____71111
                        in
                     uu____71106 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____71163 =
                            let uu____71164 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____71164  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____71163) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____71177 =
                              let uu____71180 =
                                let uu____71185 =
                                  let uu____71186 =
                                    let uu____71195 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____71195
                                     in
                                  [uu____71186]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____71185
                                 in
                              uu____71180 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____71177)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_71220 = fml  in
                     let uu____71221 =
                       let uu____71222 =
                         let uu____71229 =
                           let uu____71230 =
                             let uu____71243 =
                               let uu____71254 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____71254]  in
                             [uu____71243]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____71230  in
                         (fml, uu____71229)  in
                       FStar_Syntax_Syntax.Tm_meta uu____71222  in
                     {
                       FStar_Syntax_Syntax.n = uu____71221;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_71220.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_71220.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71309 =
                              let uu____71314 =
                                let uu____71315 =
                                  let uu____71324 =
                                    let uu____71325 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71325
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71324  in
                                [uu____71315]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71314
                               in
                            uu____71309 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71382 =
                              let uu____71387 =
                                let uu____71388 =
                                  let uu____71397 =
                                    let uu____71398 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71398
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71397  in
                                [uu____71388]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71387
                               in
                            uu____71382 FStar_Pervasives_Native.None
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
          let uu____71475 =
            let uu____71476 = FStar_Syntax_Subst.compress dt1  in
            uu____71476.FStar_Syntax_Syntax.n  in
          match uu____71475 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____71480) ->
              let dbs1 =
                let uu____71510 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____71510  in
              let dbs2 =
                let uu____71560 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____71560 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____71575 =
                           let uu____71580 =
                             let uu____71581 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____71581]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____71580
                            in
                         uu____71575 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____71614 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____71614 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____71624 =
                       let uu____71629 =
                         let uu____71630 =
                           let uu____71639 =
                             let uu____71640 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____71640
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____71639  in
                         [uu____71630]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____71629
                        in
                     uu____71624 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____71689 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____71780,uu____71781,uu____71782,uu____71783,uu____71784)
                  -> lid
              | uu____71793 -> failwith "Impossible!"  in
            let uu____71795 = acc  in
            match uu____71795 with
            | (uu____71832,en,uu____71834,uu____71835) ->
                let uu____71856 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____71856 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____71893 = acc  in
                     (match uu____71893 with
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
                                     (uu____71968,uu____71969,uu____71970,t_lid,uu____71972,uu____71973)
                                     -> t_lid = lid
                                 | uu____71980 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____71995 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____71995)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____71998 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____72001 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____71998, uu____72001)))
  
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
          let uu____72059 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____72069,us,uu____72071,t,uu____72073,uu____72074) ->
                (us, t)
            | uu____72083 -> failwith "Impossible!"  in
          match uu____72059 with
          | (us,t) ->
              let uu____72093 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____72093 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____72119 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____72119 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____72197 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____72197 with
                           | (uu____72212,t1) ->
                               let uu____72234 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____72234
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____72239 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____72239 with
                          | (phi1,uu____72247) ->
                              ((let uu____72249 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____72249
                                then
                                  let uu____72252 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____72252
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____72270  ->
                                         match uu____72270 with
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
                let uu____72342 =
                  let uu____72343 = FStar_Syntax_Subst.compress t  in
                  uu____72343.FStar_Syntax_Syntax.n  in
                match uu____72342 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____72351) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____72388 = is_mutual t'  in
                    if uu____72388
                    then true
                    else
                      (let uu____72395 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____72395)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____72415) ->
                    is_mutual t'
                | uu____72420 -> false
              
              and exists_mutual uu___586_72422 =
                match uu___586_72422 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____72443 =
                let uu____72444 = FStar_Syntax_Subst.compress dt1  in
                uu____72444.FStar_Syntax_Syntax.n  in
              match uu____72443 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____72450) ->
                  let dbs1 =
                    let uu____72480 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____72480  in
                  let dbs2 =
                    let uu____72530 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____72530 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____72550 =
                               let uu____72555 =
                                 let uu____72556 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____72556]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____72555
                                in
                             uu____72550 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____72588 = is_mutual sort  in
                             if uu____72588
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
                           let uu____72603 =
                             let uu____72608 =
                               let uu____72609 =
                                 let uu____72618 =
                                   let uu____72619 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____72619 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____72618  in
                               [uu____72609]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____72608
                              in
                           uu____72603 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____72668 -> acc
  
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
              let uu____72718 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____72740,bs,t,uu____72743,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____72755 -> failwith "Impossible!"  in
              match uu____72718 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____72779 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____72779 t  in
                  let uu____72788 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____72788 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____72798 =
                           let uu____72799 = FStar_Syntax_Subst.compress t2
                              in
                           uu____72799.FStar_Syntax_Syntax.n  in
                         match uu____72798 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____72803) ->
                             ibs
                         | uu____72824 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____72833 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____72834 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____72833
                           uu____72834
                          in
                       let ind1 =
                         let uu____72840 =
                           let uu____72845 =
                             FStar_List.map
                               (fun uu____72862  ->
                                  match uu____72862 with
                                  | (bv,aq) ->
                                      let uu____72881 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72881, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____72845  in
                         uu____72840 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____72889 =
                           let uu____72894 =
                             FStar_List.map
                               (fun uu____72911  ->
                                  match uu____72911 with
                                  | (bv,aq) ->
                                      let uu____72930 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72930, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____72894  in
                         uu____72889 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____72938 =
                           let uu____72943 =
                             let uu____72944 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____72944]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____72943
                            in
                         uu____72938 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____72983,uu____72984,uu____72985,t_lid,uu____72987,uu____72988)
                                  -> t_lid = lid
                              | uu____72995 -> failwith "Impossible")
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
                         let uu___1460_73007 = fml  in
                         let uu____73008 =
                           let uu____73009 =
                             let uu____73016 =
                               let uu____73017 =
                                 let uu____73030 =
                                   let uu____73041 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____73041]  in
                                 [uu____73030]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____73017
                                in
                             (fml, uu____73016)  in
                           FStar_Syntax_Syntax.Tm_meta uu____73009  in
                         {
                           FStar_Syntax_Syntax.n = uu____73008;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_73007.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_73007.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73096 =
                                  let uu____73101 =
                                    let uu____73102 =
                                      let uu____73111 =
                                        let uu____73112 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73112
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73111
                                       in
                                    [uu____73102]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73101
                                   in
                                uu____73096 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73169 =
                                  let uu____73174 =
                                    let uu____73175 =
                                      let uu____73184 =
                                        let uu____73185 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73185
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73184
                                       in
                                    [uu____73175]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73174
                                   in
                                uu____73169 FStar_Pervasives_Native.None
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
                     (lid,uu____73279,uu____73280,uu____73281,uu____73282,uu____73283)
                     -> lid
                 | uu____73292 -> failwith "Impossible!") tcs
             in
          let uu____73294 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____73306,uu____73307,uu____73308,uu____73309) ->
                (lid, us)
            | uu____73318 -> failwith "Impossible!"  in
          match uu____73294 with
          | (lid,us) ->
              let uu____73328 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____73328 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____73355 =
                       let uu____73356 =
                         let uu____73363 = get_haseq_axiom_lid lid  in
                         (uu____73363, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____73356  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____73355;
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
          let uu____73417 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_73442  ->
                    match uu___587_73442 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____73444;
                        FStar_Syntax_Syntax.sigrng = uu____73445;
                        FStar_Syntax_Syntax.sigquals = uu____73446;
                        FStar_Syntax_Syntax.sigmeta = uu____73447;
                        FStar_Syntax_Syntax.sigattrs = uu____73448;_} -> true
                    | uu____73470 -> false))
             in
          match uu____73417 with
          | (tys,datas) ->
              ((let uu____73493 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_73504  ->
                          match uu___588_73504 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____73506;
                              FStar_Syntax_Syntax.sigrng = uu____73507;
                              FStar_Syntax_Syntax.sigquals = uu____73508;
                              FStar_Syntax_Syntax.sigmeta = uu____73509;
                              FStar_Syntax_Syntax.sigattrs = uu____73510;_}
                              -> false
                          | uu____73531 -> true))
                   in
                if uu____73493
                then
                  let uu____73534 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____73534
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____73549 =
                       let uu____73550 = FStar_List.hd tys  in
                       uu____73550.FStar_Syntax_Syntax.sigel  in
                     match uu____73549 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____73553,uvs,uu____73555,uu____73556,uu____73557,uu____73558)
                         -> uvs
                     | uu____73567 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____73572 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____73602 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____73602 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____73640,bs,t,l1,l2) ->
                                      let uu____73653 =
                                        let uu____73670 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____73671 =
                                          let uu____73672 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____73672 t
                                           in
                                        (lid, univs2, uu____73670,
                                          uu____73671, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____73653
                                  | uu____73685 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_73687 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_73687.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_73687.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_73687.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_73687.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____73697,t,lid_t,x,l) ->
                                      let uu____73708 =
                                        let uu____73724 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____73724, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____73708
                                  | uu____73728 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_73730 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_73730.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_73730.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_73730.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_73730.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____73731 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____73731, tys1, datas1))
                   in
                match uu____73572 with
                | (env1,tys1,datas1) ->
                    let uu____73757 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____73796  ->
                             match uu____73796 with
                             | (env2,all_tcs,g) ->
                                 let uu____73836 = tc_tycon env2 tc  in
                                 (match uu____73836 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____73863 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____73863
                                        then
                                          let uu____73866 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____73866
                                        else ());
                                       (let uu____73871 =
                                          let uu____73872 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____73872
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____73871))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____73757 with
                     | (env2,tcs,g) ->
                         let uu____73918 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____73940  ->
                                  match uu____73940 with
                                  | (datas2,g1) ->
                                      let uu____73959 =
                                        let uu____73964 = tc_data env2 tcs
                                           in
                                        uu____73964 se  in
                                      (match uu____73959 with
                                       | (data,g') ->
                                           let uu____73981 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____73981)))
                             datas1 ([], g)
                            in
                         (match uu____73918 with
                          | (datas2,g1) ->
                              let uu____74002 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____74024 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____74024, datas2))
                                 in
                              (match uu____74002 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____74056 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____74057 =
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
                                         uu____74056;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____74057
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____74083,uu____74084)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____74104 =
                                                    let uu____74110 =
                                                      let uu____74112 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____74114 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____74112
                                                        uu____74114
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____74110)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____74104
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____74118 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____74118 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____74134)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____74165 ->
                                                             let uu____74166
                                                               =
                                                               let uu____74173
                                                                 =
                                                                 let uu____74174
                                                                   =
                                                                   let uu____74189
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____74189)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____74174
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____74173
                                                                in
                                                             uu____74166
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
                                                       let uu____74214 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____74214
                                                        with
                                                        | (uu____74219,inferred)
                                                            ->
                                                            let uu____74221 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____74221
                                                             with
                                                             | (uu____74226,expected)
                                                                 ->
                                                                 let uu____74228
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____74228
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____74235 -> ()));
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
                          let uu____74346 =
                            let uu____74353 =
                              let uu____74354 =
                                let uu____74361 =
                                  let uu____74364 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____74364
                                   in
                                (uu____74361, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____74354  in
                            FStar_Syntax_Syntax.mk uu____74353  in
                          uu____74346 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____74401  ->
                                  match uu____74401 with
                                  | (x,imp) ->
                                      let uu____74420 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____74420, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____74424 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____74424  in
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
                               let uu____74447 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____74447
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____74449 =
                               let uu____74452 =
                                 let uu____74455 =
                                   let uu____74460 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____74461 =
                                     let uu____74462 =
                                       let uu____74471 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____74471
                                        in
                                     [uu____74462]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____74460
                                     uu____74461
                                    in
                                 uu____74455 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____74452  in
                             FStar_Syntax_Util.refine x uu____74449  in
                           let uu____74498 =
                             let uu___1671_74499 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_74499.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_74499.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____74498)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____74516 =
                          FStar_List.map
                            (fun uu____74540  ->
                               match uu____74540 with
                               | (x,uu____74554) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____74516 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____74613  ->
                                match uu____74613 with
                                | (x,uu____74627) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____74638 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____74638)
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
                               (let uu____74659 =
                                  let uu____74661 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____74661.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____74659)
                              in
                           let quals =
                             let uu____74665 =
                               FStar_List.filter
                                 (fun uu___589_74669  ->
                                    match uu___589_74669 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____74674 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____74665
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____74712 =
                                 let uu____74713 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____74713  in
                               FStar_Syntax_Syntax.mk_Total uu____74712  in
                             let uu____74714 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____74714
                              in
                           let decl =
                             let uu____74718 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____74718;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____74720 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____74720
                            then
                              let uu____74724 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____74724
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
                                             fun uu____74785  ->
                                               match uu____74785 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____74814 =
                                                       let uu____74817 =
                                                         let uu____74818 =
                                                           let uu____74825 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____74825,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____74818
                                                          in
                                                       pos uu____74817  in
                                                     (uu____74814, b)
                                                   else
                                                     (let uu____74833 =
                                                        let uu____74836 =
                                                          let uu____74837 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____74837
                                                           in
                                                        pos uu____74836  in
                                                      (uu____74833, b))))
                                      in
                                   let pat_true =
                                     let uu____74856 =
                                       let uu____74859 =
                                         let uu____74860 =
                                           let uu____74874 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____74874, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____74860
                                          in
                                       pos uu____74859  in
                                     (uu____74856,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____74909 =
                                       let uu____74912 =
                                         let uu____74913 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____74913
                                          in
                                       pos uu____74912  in
                                     (uu____74909,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____74927 =
                                     let uu____74934 =
                                       let uu____74935 =
                                         let uu____74958 =
                                           let uu____74975 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____74990 =
                                             let uu____75007 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____75007]  in
                                           uu____74975 :: uu____74990  in
                                         (arg_exp, uu____74958)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____74935
                                        in
                                     FStar_Syntax_Syntax.mk uu____74934  in
                                   uu____74927 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____75086 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____75086
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
                                let uu____75108 =
                                  let uu____75113 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____75113  in
                                let uu____75114 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____75108
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____75114 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____75120 =
                                  let uu____75121 =
                                    let uu____75128 =
                                      let uu____75131 =
                                        let uu____75132 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____75132
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____75131]  in
                                    ((false, [lb]), uu____75128)  in
                                  FStar_Syntax_Syntax.Sig_let uu____75121  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____75120;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____75146 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____75146
                               then
                                 let uu____75150 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____75150
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
                                fun uu____75223  ->
                                  match uu____75223 with
                                  | (a,uu____75232) ->
                                      let uu____75237 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____75237 with
                                       | (field_name,uu____75243) ->
                                           let field_proj_tm =
                                             let uu____75245 =
                                               let uu____75246 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____75246
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____75245 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____75272 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____75314  ->
                                    match uu____75314 with
                                    | (x,uu____75325) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____75331 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____75331 with
                                         | (field_name,uu____75339) ->
                                             let t =
                                               let uu____75343 =
                                                 let uu____75344 =
                                                   let uu____75347 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____75347
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____75344
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____75343
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____75353 =
                                                    let uu____75355 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____75355.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____75353)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____75374 =
                                                   FStar_List.filter
                                                     (fun uu___590_75378  ->
                                                        match uu___590_75378
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____75381 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____75374
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_75396  ->
                                                         match uu___591_75396
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____75402 ->
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
                                               let uu____75413 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____75413;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____75415 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____75415
                                               then
                                                 let uu____75419 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____75419
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
                                                           fun uu____75473 
                                                             ->
                                                             match uu____75473
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
                                                                   let uu____75503
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____75503,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____75523
                                                                    =
                                                                    let uu____75526
                                                                    =
                                                                    let uu____75527
                                                                    =
                                                                    let uu____75534
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____75534,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____75527
                                                                     in
                                                                    pos
                                                                    uu____75526
                                                                     in
                                                                    (uu____75523,
                                                                    b))
                                                                   else
                                                                    (let uu____75542
                                                                    =
                                                                    let uu____75545
                                                                    =
                                                                    let uu____75546
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____75546
                                                                     in
                                                                    pos
                                                                    uu____75545
                                                                     in
                                                                    (uu____75542,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____75565 =
                                                     let uu____75568 =
                                                       let uu____75569 =
                                                         let uu____75583 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____75583,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____75569
                                                        in
                                                     pos uu____75568  in
                                                   let uu____75593 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____75565,
                                                     FStar_Pervasives_Native.None,
                                                     uu____75593)
                                                    in
                                                 let body =
                                                   let uu____75609 =
                                                     let uu____75616 =
                                                       let uu____75617 =
                                                         let uu____75640 =
                                                           let uu____75657 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____75657]  in
                                                         (arg_exp,
                                                           uu____75640)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____75617
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____75616
                                                      in
                                                   uu____75609
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____75725 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____75725
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
                                                   let uu____75744 =
                                                     let uu____75749 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____75749
                                                      in
                                                   let uu____75750 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____75744;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____75750;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____75756 =
                                                     let uu____75757 =
                                                       let uu____75764 =
                                                         let uu____75767 =
                                                           let uu____75768 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____75768
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____75767]  in
                                                       ((false, [lb]),
                                                         uu____75764)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____75757
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____75756;
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
                                                 (let uu____75782 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____75782
                                                  then
                                                    let uu____75786 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____75786
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____75272 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____75840) when
              let uu____75847 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____75847 ->
              let uu____75849 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____75849 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____75871 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____75871 with
                    | (formals,uu____75889) ->
                        let uu____75910 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____75945 =
                                   let uu____75947 =
                                     let uu____75948 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____75948  in
                                   FStar_Ident.lid_equals typ_lid uu____75947
                                    in
                                 if uu____75945
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____75970,uvs',tps,typ0,uu____75974,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____75994 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____76043 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____76043
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____75910 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____76081 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____76081 with
                              | (indices,uu____76099) ->
                                  let refine_domain =
                                    let uu____76122 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_76129  ->
                                              match uu___592_76129 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____76131 -> true
                                              | uu____76141 -> false))
                                       in
                                    if uu____76122
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_76156 =
                                      match uu___593_76156 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____76159,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____76171 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____76172 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____76172 with
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
                                    let uu____76185 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____76185 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____76268  ->
                                               fun uu____76269  ->
                                                 match (uu____76268,
                                                         uu____76269)
                                                 with
                                                 | ((x,uu____76295),(x',uu____76297))
                                                     ->
                                                     let uu____76318 =
                                                       let uu____76325 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____76325)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____76318) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____76330 -> []
  