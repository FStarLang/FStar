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
          let uu____66280 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____66280 with
           | (usubst,uvs1) ->
               let uu____66307 =
                 let uu____66314 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____66315 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____66316 =
                   let uu____66317 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____66317 k  in
                 (uu____66314, uu____66315, uu____66316)  in
               (match uu____66307 with
                | (env1,tps1,k1) ->
                    let uu____66337 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____66337 with
                     | (tps2,k2) ->
                         let uu____66352 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____66352 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____66373 =
                                let uu____66392 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____66392 with
                                | (k3,uu____66418,g) ->
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
                                    let uu____66421 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____66436 =
                                      let uu____66437 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____66437
                                       in
                                    (uu____66421, uu____66436)
                                 in
                              (match uu____66373 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____66500 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____66500
                                      in
                                   let uu____66503 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____66503 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____66521 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____66521))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____66528 =
                                              let uu____66534 =
                                                let uu____66536 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____66538 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____66536 uu____66538
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____66534)
                                               in
                                            FStar_Errors.raise_error
                                              uu____66528
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
                                            let uu____66551 =
                                              let uu____66560 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____66577 =
                                                let uu____66586 =
                                                  let uu____66599 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____66599
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____66586
                                                 in
                                              FStar_List.append uu____66560
                                                uu____66577
                                               in
                                            let uu____66622 =
                                              let uu____66625 =
                                                let uu____66626 =
                                                  let uu____66631 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____66631
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____66626
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____66625
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____66551 uu____66622
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____66648 =
                                            let uu____66653 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____66654 =
                                              let uu____66655 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____66655 k4
                                               in
                                            (uu____66653, uu____66654)  in
                                          match uu____66648 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____66675 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____66675,
                                                (let uu___646_66681 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_66681.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_66681.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_66681.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_66681.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____66686 -> failwith "impossible"
  
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
            let uu____66750 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____66750 with
             | (usubst,_uvs1) ->
                 let uu____66773 =
                   let uu____66778 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____66779 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____66778, uu____66779)  in
                 (match uu____66773 with
                  | (env1,t1) ->
                      let uu____66786 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____66825  ->
                               match uu____66825 with
                               | (se1,u_tc) ->
                                   let uu____66840 =
                                     let uu____66842 =
                                       let uu____66843 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____66843  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____66842
                                      in
                                   if uu____66840
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____66863,uu____66864,tps,uu____66866,uu____66867,uu____66868)
                                          ->
                                          let tps1 =
                                            let uu____66878 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____66878
                                              (FStar_List.map
                                                 (fun uu____66918  ->
                                                    match uu____66918 with
                                                    | (x,uu____66932) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____66940 =
                                            let uu____66947 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____66947, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____66940
                                      | uu____66954 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____66997 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____66997
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____66786 with
                       | (env2,tps,u_tc) ->
                           let uu____67029 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____67045 =
                               let uu____67046 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____67046.FStar_Syntax_Syntax.n  in
                             match uu____67045 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____67085 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____67085 with
                                  | (uu____67126,bs') ->
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
                                                fun uu____67197  ->
                                                  match uu____67197 with
                                                  | (x,uu____67206) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____67213 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____67213)
                             | uu____67214 -> ([], t2)  in
                           (match uu____67029 with
                            | (arguments,result) ->
                                ((let uu____67258 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____67258
                                  then
                                    let uu____67261 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____67263 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____67266 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____67261 uu____67263 uu____67266
                                  else ());
                                 (let uu____67271 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____67271 with
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
                                      let uu____67289 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____67289 with
                                       | (result1,res_lcomp) ->
                                           let uu____67300 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____67300 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____67358 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____67358
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____67440  ->
                                                      fun uu____67441  ->
                                                        match (uu____67440,
                                                                uu____67441)
                                                        with
                                                        | ((bv,uu____67471),
                                                           (t2,uu____67473))
                                                            ->
                                                            let uu____67500 =
                                                              let uu____67501
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____67501.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____67500
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____67505 ->
                                                                 let uu____67506
                                                                   =
                                                                   let uu____67512
                                                                    =
                                                                    let uu____67514
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____67516
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____67514
                                                                    uu____67516
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____67512)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____67506
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____67521 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____67521
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____67523 =
                                                     let uu____67524 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____67524.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____67523 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____67527 -> ()
                                                   | uu____67528 ->
                                                       let uu____67529 =
                                                         let uu____67535 =
                                                           let uu____67537 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____67539 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____67537
                                                             uu____67539
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____67535)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____67529
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____67544 =
                                                       let uu____67545 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____67545.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____67544 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____67549;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____67550;_},tuvs)
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
                                                                    let uu____67564
                                                                    =
                                                                    let uu____67565
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____67566
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
                                                                    uu____67565
                                                                    uu____67566
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67564)
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
                                                     | uu____67572 ->
                                                         let uu____67573 =
                                                           let uu____67579 =
                                                             let uu____67581
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____67583
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____67581
                                                               uu____67583
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____67579)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____67573
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____67601  ->
                                                            fun u_x  ->
                                                              match uu____67601
                                                              with
                                                              | (x,uu____67610)
                                                                  ->
                                                                  let uu____67615
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____67615)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____67619 =
                                                       let uu____67628 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____67668 
                                                                 ->
                                                                 match uu____67668
                                                                 with
                                                                 | (x,uu____67682)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____67628
                                                         arguments1
                                                        in
                                                     let uu____67696 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____67619
                                                       uu____67696
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_67701 = se
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
                                                         (uu___768_67701.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_67701.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_67701.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_67701.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____67705 -> failwith "impossible"
  
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
            let uu___776_67772 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_67772.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_67772.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_67772.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____67782 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____67782
           then
             let uu____67787 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____67787
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____67830  ->
                     match uu____67830 with
                     | (se,uu____67836) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____67837,uu____67838,tps,k,uu____67841,uu____67842)
                              ->
                              let uu____67851 =
                                let uu____67852 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____67852
                                 in
                              FStar_Syntax_Syntax.null_binder uu____67851
                          | uu____67857 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____67886,uu____67887,t,uu____67889,uu____67890,uu____67891)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____67898 -> failwith "Impossible"))
              in
           let t =
             let uu____67903 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____67903
              in
           (let uu____67913 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____67913
            then
              let uu____67918 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____67918
            else ());
           (let uu____67923 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____67923 with
            | (uvs,t1) ->
                ((let uu____67943 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____67943
                  then
                    let uu____67948 =
                      let uu____67950 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____67950
                        (FStar_String.concat ", ")
                       in
                    let uu____67967 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____67948 uu____67967
                  else ());
                 (let uu____67972 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____67972 with
                  | (uvs1,t2) ->
                      let uu____67987 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____67987 with
                       | (args,uu____68011) ->
                           let uu____68032 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____68032 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____68137  ->
                                       fun uu____68138  ->
                                         match (uu____68137, uu____68138)
                                         with
                                         | ((x,uu____68160),(se,uu____68162))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____68178,tps,uu____68180,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____68192 =
                                                    let uu____68197 =
                                                      let uu____68198 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____68198.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____68197 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____68227 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____68227
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____68305
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____68324 -> ([], ty)
                                                     in
                                                  (match uu____68192 with
                                                   | (tps1,t3) ->
                                                       let uu___853_68333 =
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
                                                           (uu___853_68333.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_68333.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_68333.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_68333.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____68338 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____68345 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _68349  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _68349))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_68368  ->
                                                match uu___585_68368 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____68374,uu____68375,uu____68376,uu____68377,uu____68378);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____68379;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____68380;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____68381;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____68382;_}
                                                    -> (tc, uvs_universes)
                                                | uu____68395 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____68419  ->
                                           fun d  ->
                                             match uu____68419 with
                                             | (t3,uu____68428) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____68434,uu____68435,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____68446 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____68446
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_68447 = d
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
                                                          (uu___889_68447.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_68447.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_68447.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_68447.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____68451 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____68470 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____68470
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____68492 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____68492
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____68509 =
      let uu____68510 = FStar_Syntax_Subst.compress t  in
      uu____68510.FStar_Syntax_Syntax.n  in
    match uu____68509 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____68529 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____68535 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____68592 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____68661  ->
               match uu____68661 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____68705 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____68705  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____68592
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____68960 =
             let uu____68962 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____68962
              in
           debug_log env uu____68960);
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
           (let uu____68967 =
              let uu____68969 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____68969
               in
            debug_log env uu____68967);
           (let uu____68974 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____68974) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____68987 =
                  let uu____68988 = FStar_Syntax_Subst.compress btype1  in
                  uu____68988.FStar_Syntax_Syntax.n  in
                match uu____68987 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____69018 = try_get_fv t  in
                    (match uu____69018 with
                     | (fv,us) ->
                         let uu____69026 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____69026
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____69042  ->
                                 match uu____69042 with
                                 | (t1,uu____69051) ->
                                     let uu____69056 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____69056) args)
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
                          let uu____69111 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____69111
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____69115 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____69115
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
                            (fun uu____69142  ->
                               match uu____69142 with
                               | (b,uu____69151) ->
                                   let uu____69156 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____69156) sbs)
                           &&
                           ((let uu____69162 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____69162 with
                             | (uu____69168,return_type) ->
                                 let uu____69170 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____69170)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____69191 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____69195 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____69200) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____69228) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____69255,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____69314  ->
                          match uu____69314 with
                          | (p,uu____69327,t) ->
                              let bs =
                                let uu____69346 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____69346
                                 in
                              let uu____69355 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____69355 with
                               | (bs1,t1) ->
                                   let uu____69363 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____69363)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____69385,uu____69386)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____69449 ->
                    ((let uu____69451 =
                        let uu____69453 =
                          let uu____69455 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____69457 =
                            let uu____69459 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____69459  in
                          Prims.op_Hat uu____69455 uu____69457  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____69453
                         in
                      debug_log env uu____69451);
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
              (let uu____69482 =
                 let uu____69484 =
                   let uu____69486 =
                     let uu____69488 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____69488  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____69486  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____69484
                  in
               debug_log env uu____69482);
              (let uu____69492 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____69492 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____69511 =
                       let uu____69513 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____69513
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____69511
                      then
                        ((let uu____69517 =
                            let uu____69519 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____69519
                             in
                          debug_log env uu____69517);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____69530 =
                        already_unfolded ilid args unfolded env  in
                      if uu____69530
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____69561 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____69561  in
                         (let uu____69567 =
                            let uu____69569 =
                              let uu____69571 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____69571
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____69569
                             in
                          debug_log env uu____69567);
                         (let uu____69576 =
                            let uu____69577 = FStar_ST.op_Bang unfolded  in
                            let uu____69623 =
                              let uu____69630 =
                                let uu____69635 =
                                  let uu____69636 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____69636  in
                                (ilid, uu____69635)  in
                              [uu____69630]  in
                            FStar_List.append uu____69577 uu____69623  in
                          FStar_ST.op_Colon_Equals unfolded uu____69576);
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
                  (let uu____69785 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____69785 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____69808 ->
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
                         (let uu____69812 =
                            let uu____69814 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____69814
                             in
                          debug_log env uu____69812);
                         (let uu____69817 =
                            let uu____69818 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____69818.FStar_Syntax_Syntax.n  in
                          match uu____69817 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____69846 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____69846 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____69910 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____69910 dbs1
                                       in
                                    let c1 =
                                      let uu____69914 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____69914 c
                                       in
                                    let uu____69917 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____69917 with
                                     | (args1,uu____69952) ->
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
                                           let uu____70044 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____70044 c1
                                            in
                                         ((let uu____70054 =
                                             let uu____70056 =
                                               let uu____70058 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____70061 =
                                                 let uu____70063 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____70063
                                                  in
                                               Prims.op_Hat uu____70058
                                                 uu____70061
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____70056
                                              in
                                           debug_log env uu____70054);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____70097 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____70100 =
                                  let uu____70101 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____70101.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____70100
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
                   (let uu____70170 = try_get_fv t1  in
                    match uu____70170 with
                    | (fv,uu____70177) ->
                        let uu____70178 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____70178
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____70210 =
                      let uu____70212 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____70212
                       in
                    debug_log env uu____70210);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____70217 =
                      FStar_List.fold_left
                        (fun uu____70238  ->
                           fun b  ->
                             match uu____70238 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____70269 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____70293 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____70269, uu____70293))) (true, env)
                        sbs1
                       in
                    match uu____70217 with | (b,uu____70311) -> b))
              | uu____70314 ->
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
              let uu____70370 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____70370 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____70393 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____70396 =
                      let uu____70398 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____70398
                       in
                    debug_log env uu____70396);
                   (let uu____70401 =
                      let uu____70402 = FStar_Syntax_Subst.compress dt  in
                      uu____70402.FStar_Syntax_Syntax.n  in
                    match uu____70401 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____70406 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____70411) ->
                        let dbs1 =
                          let uu____70441 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____70441  in
                        let dbs2 =
                          let uu____70491 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____70491 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____70496 =
                            let uu____70498 =
                              let uu____70500 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____70500 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____70498
                             in
                          debug_log env uu____70496);
                         (let uu____70510 =
                            FStar_List.fold_left
                              (fun uu____70531  ->
                                 fun b  ->
                                   match uu____70531 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____70562 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____70586 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____70562, uu____70586)))
                              (true, env) dbs3
                             in
                          match uu____70510 with | (b,uu____70604) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____70607,uu____70608) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____70664 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____70687 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____70703,uu____70704,uu____70705) -> (lid, us, bs)
        | uu____70714 -> failwith "Impossible!"  in
      match uu____70687 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____70726 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____70726 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____70750 =
                 let uu____70753 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____70753  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____70767 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____70767
                      unfolded_inductives env2) uu____70750)
  
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
        (uu____70846,uu____70847,t,uu____70849,uu____70850,uu____70851) -> t
    | uu____70858 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____70885 =
         let uu____70887 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____70887 haseq_suffix  in
       uu____70885 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____70911 =
      let uu____70914 =
        let uu____70917 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____70917]  in
      FStar_List.append lid.FStar_Ident.ns uu____70914  in
    FStar_Ident.lid_of_ids uu____70911
  
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
          let uu____70963 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____70977,bs,t,uu____70980,uu____70981) ->
                (lid, bs, t)
            | uu____70990 -> failwith "Impossible!"  in
          match uu____70963 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____71013 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____71013 t  in
              let uu____71022 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____71022 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____71040 =
                       let uu____71041 = FStar_Syntax_Subst.compress t2  in
                       uu____71041.FStar_Syntax_Syntax.n  in
                     match uu____71040 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____71045) -> ibs
                     | uu____71066 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____71075 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____71076 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____71075 uu____71076
                      in
                   let ind1 =
                     let uu____71082 =
                       let uu____71087 =
                         FStar_List.map
                           (fun uu____71104  ->
                              match uu____71104 with
                              | (bv,aq) ->
                                  let uu____71123 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71123, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____71087  in
                     uu____71082 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____71131 =
                       let uu____71136 =
                         FStar_List.map
                           (fun uu____71153  ->
                              match uu____71153 with
                              | (bv,aq) ->
                                  let uu____71172 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____71172, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____71136  in
                     uu____71131 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____71180 =
                       let uu____71185 =
                         let uu____71186 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____71186]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____71185
                        in
                     uu____71180 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____71237 =
                            let uu____71238 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____71238  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____71237) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____71251 =
                              let uu____71254 =
                                let uu____71259 =
                                  let uu____71260 =
                                    let uu____71269 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____71269
                                     in
                                  [uu____71260]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____71259
                                 in
                              uu____71254 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____71251)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_71294 = fml  in
                     let uu____71295 =
                       let uu____71296 =
                         let uu____71303 =
                           let uu____71304 =
                             let uu____71317 =
                               let uu____71328 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____71328]  in
                             [uu____71317]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____71304  in
                         (fml, uu____71303)  in
                       FStar_Syntax_Syntax.Tm_meta uu____71296  in
                     {
                       FStar_Syntax_Syntax.n = uu____71295;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_71294.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_71294.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71383 =
                              let uu____71388 =
                                let uu____71389 =
                                  let uu____71398 =
                                    let uu____71399 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71399
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71398  in
                                [uu____71389]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71388
                               in
                            uu____71383 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____71456 =
                              let uu____71461 =
                                let uu____71462 =
                                  let uu____71471 =
                                    let uu____71472 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____71472
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____71471  in
                                [uu____71462]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____71461
                               in
                            uu____71456 FStar_Pervasives_Native.None
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
          let uu____71549 =
            let uu____71550 = FStar_Syntax_Subst.compress dt1  in
            uu____71550.FStar_Syntax_Syntax.n  in
          match uu____71549 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____71554) ->
              let dbs1 =
                let uu____71584 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____71584  in
              let dbs2 =
                let uu____71634 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____71634 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____71649 =
                           let uu____71654 =
                             let uu____71655 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____71655]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____71654
                            in
                         uu____71649 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____71688 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____71688 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____71698 =
                       let uu____71703 =
                         let uu____71704 =
                           let uu____71713 =
                             let uu____71714 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____71714
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____71713  in
                         [uu____71704]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____71703
                        in
                     uu____71698 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____71763 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____71854,uu____71855,uu____71856,uu____71857,uu____71858)
                  -> lid
              | uu____71867 -> failwith "Impossible!"  in
            let uu____71869 = acc  in
            match uu____71869 with
            | (uu____71906,en,uu____71908,uu____71909) ->
                let uu____71930 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____71930 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____71967 = acc  in
                     (match uu____71967 with
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
                                     (uu____72042,uu____72043,uu____72044,t_lid,uu____72046,uu____72047)
                                     -> t_lid = lid
                                 | uu____72054 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____72069 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____72069)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____72072 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____72075 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____72072, uu____72075)))
  
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
          let uu____72133 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____72143,us,uu____72145,t,uu____72147,uu____72148) ->
                (us, t)
            | uu____72157 -> failwith "Impossible!"  in
          match uu____72133 with
          | (us,t) ->
              let uu____72167 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____72167 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____72193 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____72193 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____72271 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____72271 with
                           | (uu____72286,t1) ->
                               let uu____72308 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____72308
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____72313 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____72313 with
                          | (phi1,uu____72321) ->
                              ((let uu____72323 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____72323
                                then
                                  let uu____72326 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____72326
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____72344  ->
                                         match uu____72344 with
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
                let uu____72416 =
                  let uu____72417 = FStar_Syntax_Subst.compress t  in
                  uu____72417.FStar_Syntax_Syntax.n  in
                match uu____72416 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____72425) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____72462 = is_mutual t'  in
                    if uu____72462
                    then true
                    else
                      (let uu____72469 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____72469)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____72489) ->
                    is_mutual t'
                | uu____72494 -> false
              
              and exists_mutual uu___586_72496 =
                match uu___586_72496 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____72517 =
                let uu____72518 = FStar_Syntax_Subst.compress dt1  in
                uu____72518.FStar_Syntax_Syntax.n  in
              match uu____72517 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____72524) ->
                  let dbs1 =
                    let uu____72554 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____72554  in
                  let dbs2 =
                    let uu____72604 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____72604 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____72624 =
                               let uu____72629 =
                                 let uu____72630 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____72630]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____72629
                                in
                             uu____72624 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____72662 = is_mutual sort  in
                             if uu____72662
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
                           let uu____72677 =
                             let uu____72682 =
                               let uu____72683 =
                                 let uu____72692 =
                                   let uu____72693 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____72693 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____72692  in
                               [uu____72683]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____72682
                              in
                           uu____72677 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____72742 -> acc
  
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
              let uu____72792 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____72814,bs,t,uu____72817,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____72829 -> failwith "Impossible!"  in
              match uu____72792 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____72853 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____72853 t  in
                  let uu____72862 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____72862 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____72872 =
                           let uu____72873 = FStar_Syntax_Subst.compress t2
                              in
                           uu____72873.FStar_Syntax_Syntax.n  in
                         match uu____72872 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____72877) ->
                             ibs
                         | uu____72898 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____72907 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____72908 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____72907
                           uu____72908
                          in
                       let ind1 =
                         let uu____72914 =
                           let uu____72919 =
                             FStar_List.map
                               (fun uu____72936  ->
                                  match uu____72936 with
                                  | (bv,aq) ->
                                      let uu____72955 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____72955, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____72919  in
                         uu____72914 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____72963 =
                           let uu____72968 =
                             FStar_List.map
                               (fun uu____72985  ->
                                  match uu____72985 with
                                  | (bv,aq) ->
                                      let uu____73004 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____73004, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____72968  in
                         uu____72963 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____73012 =
                           let uu____73017 =
                             let uu____73018 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____73018]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____73017
                            in
                         uu____73012 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____73057,uu____73058,uu____73059,t_lid,uu____73061,uu____73062)
                                  -> t_lid = lid
                              | uu____73069 -> failwith "Impossible")
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
                         let uu___1460_73081 = fml  in
                         let uu____73082 =
                           let uu____73083 =
                             let uu____73090 =
                               let uu____73091 =
                                 let uu____73104 =
                                   let uu____73115 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____73115]  in
                                 [uu____73104]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____73091
                                in
                             (fml, uu____73090)  in
                           FStar_Syntax_Syntax.Tm_meta uu____73083  in
                         {
                           FStar_Syntax_Syntax.n = uu____73082;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_73081.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_73081.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73170 =
                                  let uu____73175 =
                                    let uu____73176 =
                                      let uu____73185 =
                                        let uu____73186 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73186
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73185
                                       in
                                    [uu____73176]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73175
                                   in
                                uu____73170 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____73243 =
                                  let uu____73248 =
                                    let uu____73249 =
                                      let uu____73258 =
                                        let uu____73259 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____73259
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____73258
                                       in
                                    [uu____73249]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____73248
                                   in
                                uu____73243 FStar_Pervasives_Native.None
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
                     (lid,uu____73353,uu____73354,uu____73355,uu____73356,uu____73357)
                     -> lid
                 | uu____73366 -> failwith "Impossible!") tcs
             in
          let uu____73368 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____73380,uu____73381,uu____73382,uu____73383) ->
                (lid, us)
            | uu____73392 -> failwith "Impossible!"  in
          match uu____73368 with
          | (lid,us) ->
              let uu____73402 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____73402 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____73429 =
                       let uu____73430 =
                         let uu____73437 = get_haseq_axiom_lid lid  in
                         (uu____73437, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____73430  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____73429;
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
          let uu____73491 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_73516  ->
                    match uu___587_73516 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____73518;
                        FStar_Syntax_Syntax.sigrng = uu____73519;
                        FStar_Syntax_Syntax.sigquals = uu____73520;
                        FStar_Syntax_Syntax.sigmeta = uu____73521;
                        FStar_Syntax_Syntax.sigattrs = uu____73522;_} -> true
                    | uu____73544 -> false))
             in
          match uu____73491 with
          | (tys,datas) ->
              ((let uu____73567 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_73578  ->
                          match uu___588_73578 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____73580;
                              FStar_Syntax_Syntax.sigrng = uu____73581;
                              FStar_Syntax_Syntax.sigquals = uu____73582;
                              FStar_Syntax_Syntax.sigmeta = uu____73583;
                              FStar_Syntax_Syntax.sigattrs = uu____73584;_}
                              -> false
                          | uu____73605 -> true))
                   in
                if uu____73567
                then
                  let uu____73608 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____73608
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____73623 =
                       let uu____73624 = FStar_List.hd tys  in
                       uu____73624.FStar_Syntax_Syntax.sigel  in
                     match uu____73623 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____73627,uvs,uu____73629,uu____73630,uu____73631,uu____73632)
                         -> uvs
                     | uu____73641 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____73646 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____73676 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____73676 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____73714,bs,t,l1,l2) ->
                                      let uu____73727 =
                                        let uu____73744 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____73745 =
                                          let uu____73746 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____73746 t
                                           in
                                        (lid, univs2, uu____73744,
                                          uu____73745, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____73727
                                  | uu____73759 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_73761 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_73761.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_73761.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_73761.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_73761.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____73771,t,lid_t,x,l) ->
                                      let uu____73782 =
                                        let uu____73798 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____73798, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____73782
                                  | uu____73802 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_73804 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_73804.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_73804.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_73804.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_73804.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____73805 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____73805, tys1, datas1))
                   in
                match uu____73646 with
                | (env1,tys1,datas1) ->
                    let uu____73831 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____73870  ->
                             match uu____73870 with
                             | (env2,all_tcs,g) ->
                                 let uu____73910 = tc_tycon env2 tc  in
                                 (match uu____73910 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____73937 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____73937
                                        then
                                          let uu____73940 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____73940
                                        else ());
                                       (let uu____73945 =
                                          let uu____73946 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____73946
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____73945))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____73831 with
                     | (env2,tcs,g) ->
                         let uu____73992 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____74014  ->
                                  match uu____74014 with
                                  | (datas2,g1) ->
                                      let uu____74033 =
                                        let uu____74038 = tc_data env2 tcs
                                           in
                                        uu____74038 se  in
                                      (match uu____74033 with
                                       | (data,g') ->
                                           let uu____74055 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____74055)))
                             datas1 ([], g)
                            in
                         (match uu____73992 with
                          | (datas2,g1) ->
                              let uu____74076 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____74098 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____74098, datas2))
                                 in
                              (match uu____74076 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____74130 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____74131 =
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
                                         uu____74130;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____74131
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____74157,uu____74158)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____74178 =
                                                    let uu____74184 =
                                                      let uu____74186 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____74188 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____74186
                                                        uu____74188
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____74184)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____74178
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____74192 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____74192 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____74208)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____74239 ->
                                                             let uu____74240
                                                               =
                                                               let uu____74247
                                                                 =
                                                                 let uu____74248
                                                                   =
                                                                   let uu____74263
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____74263)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____74248
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____74247
                                                                in
                                                             uu____74240
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
                                                       let uu____74288 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____74288
                                                        with
                                                        | (uu____74293,inferred)
                                                            ->
                                                            let uu____74295 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____74295
                                                             with
                                                             | (uu____74300,expected)
                                                                 ->
                                                                 let uu____74302
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____74302
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____74309 -> ()));
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
                          let uu____74420 =
                            let uu____74427 =
                              let uu____74428 =
                                let uu____74435 =
                                  let uu____74438 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____74438
                                   in
                                (uu____74435, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____74428  in
                            FStar_Syntax_Syntax.mk uu____74427  in
                          uu____74420 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____74475  ->
                                  match uu____74475 with
                                  | (x,imp) ->
                                      let uu____74494 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____74494, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____74498 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____74498  in
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
                               let uu____74521 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____74521
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____74523 =
                               let uu____74526 =
                                 let uu____74529 =
                                   let uu____74534 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____74535 =
                                     let uu____74536 =
                                       let uu____74545 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____74545
                                        in
                                     [uu____74536]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____74534
                                     uu____74535
                                    in
                                 uu____74529 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____74526  in
                             FStar_Syntax_Util.refine x uu____74523  in
                           let uu____74572 =
                             let uu___1671_74573 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_74573.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_74573.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____74572)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____74590 =
                          FStar_List.map
                            (fun uu____74614  ->
                               match uu____74614 with
                               | (x,uu____74628) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____74590 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____74687  ->
                                match uu____74687 with
                                | (x,uu____74701) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____74712 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____74712)
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
                               (let uu____74733 =
                                  let uu____74735 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____74735.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____74733)
                              in
                           let quals =
                             let uu____74739 =
                               FStar_List.filter
                                 (fun uu___589_74743  ->
                                    match uu___589_74743 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____74748 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____74739
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____74786 =
                                 let uu____74787 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____74787  in
                               FStar_Syntax_Syntax.mk_Total uu____74786  in
                             let uu____74788 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____74788
                              in
                           let decl =
                             let uu____74792 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____74792;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____74794 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____74794
                            then
                              let uu____74798 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____74798
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
                                             fun uu____74859  ->
                                               match uu____74859 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____74888 =
                                                       let uu____74891 =
                                                         let uu____74892 =
                                                           let uu____74899 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____74899,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____74892
                                                          in
                                                       pos uu____74891  in
                                                     (uu____74888, b)
                                                   else
                                                     (let uu____74907 =
                                                        let uu____74910 =
                                                          let uu____74911 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____74911
                                                           in
                                                        pos uu____74910  in
                                                      (uu____74907, b))))
                                      in
                                   let pat_true =
                                     let uu____74930 =
                                       let uu____74933 =
                                         let uu____74934 =
                                           let uu____74948 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____74948, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____74934
                                          in
                                       pos uu____74933  in
                                     (uu____74930,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____74983 =
                                       let uu____74986 =
                                         let uu____74987 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____74987
                                          in
                                       pos uu____74986  in
                                     (uu____74983,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____75001 =
                                     let uu____75008 =
                                       let uu____75009 =
                                         let uu____75032 =
                                           let uu____75049 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____75064 =
                                             let uu____75081 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____75081]  in
                                           uu____75049 :: uu____75064  in
                                         (arg_exp, uu____75032)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____75009
                                        in
                                     FStar_Syntax_Syntax.mk uu____75008  in
                                   uu____75001 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____75160 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____75160
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
                                let uu____75182 =
                                  let uu____75187 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____75187  in
                                let uu____75188 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____75182
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____75188 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____75194 =
                                  let uu____75195 =
                                    let uu____75202 =
                                      let uu____75205 =
                                        let uu____75206 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____75206
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____75205]  in
                                    ((false, [lb]), uu____75202)  in
                                  FStar_Syntax_Syntax.Sig_let uu____75195  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____75194;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____75220 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____75220
                               then
                                 let uu____75224 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____75224
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
                                fun uu____75297  ->
                                  match uu____75297 with
                                  | (a,uu____75306) ->
                                      let uu____75311 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____75311 with
                                       | (field_name,uu____75317) ->
                                           let field_proj_tm =
                                             let uu____75319 =
                                               let uu____75320 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____75320
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____75319 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____75346 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____75388  ->
                                    match uu____75388 with
                                    | (x,uu____75399) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____75405 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____75405 with
                                         | (field_name,uu____75413) ->
                                             let t =
                                               let uu____75417 =
                                                 let uu____75418 =
                                                   let uu____75421 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____75421
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____75418
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____75417
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____75427 =
                                                    let uu____75429 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____75429.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____75427)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____75448 =
                                                   FStar_List.filter
                                                     (fun uu___590_75452  ->
                                                        match uu___590_75452
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____75455 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____75448
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_75470  ->
                                                         match uu___591_75470
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____75476 ->
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
                                               let uu____75487 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____75487;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____75489 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____75489
                                               then
                                                 let uu____75493 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____75493
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
                                                           fun uu____75547 
                                                             ->
                                                             match uu____75547
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
                                                                   let uu____75577
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____75577,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____75597
                                                                    =
                                                                    let uu____75600
                                                                    =
                                                                    let uu____75601
                                                                    =
                                                                    let uu____75608
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____75608,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____75601
                                                                     in
                                                                    pos
                                                                    uu____75600
                                                                     in
                                                                    (uu____75597,
                                                                    b))
                                                                   else
                                                                    (let uu____75616
                                                                    =
                                                                    let uu____75619
                                                                    =
                                                                    let uu____75620
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____75620
                                                                     in
                                                                    pos
                                                                    uu____75619
                                                                     in
                                                                    (uu____75616,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____75639 =
                                                     let uu____75642 =
                                                       let uu____75643 =
                                                         let uu____75657 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____75657,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____75643
                                                        in
                                                     pos uu____75642  in
                                                   let uu____75667 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____75639,
                                                     FStar_Pervasives_Native.None,
                                                     uu____75667)
                                                    in
                                                 let body =
                                                   let uu____75683 =
                                                     let uu____75690 =
                                                       let uu____75691 =
                                                         let uu____75714 =
                                                           let uu____75731 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____75731]  in
                                                         (arg_exp,
                                                           uu____75714)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____75691
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____75690
                                                      in
                                                   uu____75683
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____75799 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____75799
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
                                                   let uu____75818 =
                                                     let uu____75823 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____75823
                                                      in
                                                   let uu____75824 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____75818;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____75824;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____75830 =
                                                     let uu____75831 =
                                                       let uu____75838 =
                                                         let uu____75841 =
                                                           let uu____75842 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____75842
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____75841]  in
                                                       ((false, [lb]),
                                                         uu____75838)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____75831
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____75830;
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
                                                 (let uu____75856 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____75856
                                                  then
                                                    let uu____75860 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____75860
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____75346 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____75914) when
              let uu____75921 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____75921 ->
              let uu____75923 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____75923 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____75945 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____75945 with
                    | (formals,uu____75963) ->
                        let uu____75984 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____76019 =
                                   let uu____76021 =
                                     let uu____76022 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____76022  in
                                   FStar_Ident.lid_equals typ_lid uu____76021
                                    in
                                 if uu____76019
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____76044,uvs',tps,typ0,uu____76048,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____76068 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____76117 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____76117
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____75984 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____76155 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____76155 with
                              | (indices,uu____76173) ->
                                  let refine_domain =
                                    let uu____76196 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_76203  ->
                                              match uu___592_76203 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____76205 -> true
                                              | uu____76215 -> false))
                                       in
                                    if uu____76196
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_76230 =
                                      match uu___593_76230 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____76233,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____76245 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____76246 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____76246 with
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
                                    let uu____76259 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____76259 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____76342  ->
                                               fun uu____76343  ->
                                                 match (uu____76342,
                                                         uu____76343)
                                                 with
                                                 | ((x,uu____76369),(x',uu____76371))
                                                     ->
                                                     let uu____76392 =
                                                       let uu____76399 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____76399)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____76392) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____76404 -> []
  