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
          let uu____61451 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____61451 with
           | (usubst,uvs1) ->
               let uu____61478 =
                 let uu____61485 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____61486 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____61487 =
                   let uu____61488 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____61488 k  in
                 (uu____61485, uu____61486, uu____61487)  in
               (match uu____61478 with
                | (env1,tps1,k1) ->
                    let uu____61508 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____61508 with
                     | (tps2,k2) ->
                         let uu____61523 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____61523 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____61544 =
                                let uu____61563 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____61563 with
                                | (k3,uu____61589,g) ->
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
                                    let uu____61592 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____61607 =
                                      let uu____61608 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____61608
                                       in
                                    (uu____61592, uu____61607)
                                 in
                              (match uu____61544 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____61671 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____61671
                                      in
                                   let uu____61674 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____61674 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____61692 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____61692))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____61699 =
                                              let uu____61705 =
                                                let uu____61707 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____61709 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____61707 uu____61709
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____61705)
                                               in
                                            FStar_Errors.raise_error
                                              uu____61699
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
                                            let uu____61722 =
                                              let uu____61731 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____61748 =
                                                let uu____61757 =
                                                  let uu____61770 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____61770
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____61757
                                                 in
                                              FStar_List.append uu____61731
                                                uu____61748
                                               in
                                            let uu____61793 =
                                              let uu____61796 =
                                                let uu____61797 =
                                                  let uu____61802 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____61802
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____61797
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____61796
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____61722 uu____61793
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____61819 =
                                            let uu____61824 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____61825 =
                                              let uu____61826 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____61826 k4
                                               in
                                            (uu____61824, uu____61825)  in
                                          match uu____61819 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____61846 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____61846,
                                                (let uu___646_61852 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_61852.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_61852.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_61852.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_61852.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____61857 -> failwith "impossible"
  
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
            let uu____61921 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____61921 with
             | (usubst,_uvs1) ->
                 let uu____61944 =
                   let uu____61949 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____61950 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____61949, uu____61950)  in
                 (match uu____61944 with
                  | (env1,t1) ->
                      let uu____61957 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____61996  ->
                               match uu____61996 with
                               | (se1,u_tc) ->
                                   let uu____62011 =
                                     let uu____62013 =
                                       let uu____62014 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____62014  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____62013
                                      in
                                   if uu____62011
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____62034,uu____62035,tps,uu____62037,uu____62038,uu____62039)
                                          ->
                                          let tps1 =
                                            let uu____62049 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____62049
                                              (FStar_List.map
                                                 (fun uu____62089  ->
                                                    match uu____62089 with
                                                    | (x,uu____62103) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____62111 =
                                            let uu____62118 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____62118, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____62111
                                      | uu____62125 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____62168 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____62168
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____61957 with
                       | (env2,tps,u_tc) ->
                           let uu____62200 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____62216 =
                               let uu____62217 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____62217.FStar_Syntax_Syntax.n  in
                             match uu____62216 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____62256 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____62256 with
                                  | (uu____62297,bs') ->
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
                                                fun uu____62368  ->
                                                  match uu____62368 with
                                                  | (x,uu____62377) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____62384 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____62384)
                             | uu____62385 -> ([], t2)  in
                           (match uu____62200 with
                            | (arguments,result) ->
                                ((let uu____62429 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____62429
                                  then
                                    let uu____62432 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____62434 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____62437 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____62432 uu____62434 uu____62437
                                  else ());
                                 (let uu____62442 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____62442 with
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
                                      let uu____62460 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____62460 with
                                       | (result1,res_lcomp) ->
                                           let uu____62471 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____62471 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____62529 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____62529
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____62611  ->
                                                      fun uu____62612  ->
                                                        match (uu____62611,
                                                                uu____62612)
                                                        with
                                                        | ((bv,uu____62642),
                                                           (t2,uu____62644))
                                                            ->
                                                            let uu____62671 =
                                                              let uu____62672
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____62672.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____62671
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____62676 ->
                                                                 let uu____62677
                                                                   =
                                                                   let uu____62683
                                                                    =
                                                                    let uu____62685
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____62687
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____62685
                                                                    uu____62687
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____62683)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____62677
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____62692 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____62692
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____62694 =
                                                     let uu____62695 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____62695.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____62694 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____62698 -> ()
                                                   | uu____62699 ->
                                                       let uu____62700 =
                                                         let uu____62706 =
                                                           let uu____62708 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____62710 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____62708
                                                             uu____62710
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____62706)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____62700
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____62715 =
                                                       let uu____62716 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____62716.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____62715 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____62720;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____62721;_},tuvs)
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
                                                                    let uu____62735
                                                                    =
                                                                    let uu____62736
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____62737
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
                                                                    uu____62736
                                                                    uu____62737
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62735)
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
                                                     | uu____62743 ->
                                                         let uu____62744 =
                                                           let uu____62750 =
                                                             let uu____62752
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____62754
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____62752
                                                               uu____62754
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____62750)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____62744
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____62772  ->
                                                            fun u_x  ->
                                                              match uu____62772
                                                              with
                                                              | (x,uu____62781)
                                                                  ->
                                                                  let uu____62786
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62786)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____62790 =
                                                       let uu____62799 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____62839 
                                                                 ->
                                                                 match uu____62839
                                                                 with
                                                                 | (x,uu____62853)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____62799
                                                         arguments1
                                                        in
                                                     let uu____62867 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____62790
                                                       uu____62867
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_62872 = se
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
                                                         (uu___768_62872.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_62872.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_62872.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_62872.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____62876 -> failwith "impossible"
  
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
            let uu___776_62943 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_62943.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_62943.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_62943.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____62953 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____62953
           then
             let uu____62958 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____62958
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____63001  ->
                     match uu____63001 with
                     | (se,uu____63007) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____63008,uu____63009,tps,k,uu____63012,uu____63013)
                              ->
                              let uu____63022 =
                                let uu____63023 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____63023
                                 in
                              FStar_Syntax_Syntax.null_binder uu____63022
                          | uu____63028 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____63057,uu____63058,t,uu____63060,uu____63061,uu____63062)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____63069 -> failwith "Impossible"))
              in
           let t =
             let uu____63074 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____63074
              in
           (let uu____63084 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____63084
            then
              let uu____63089 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____63089
            else ());
           (let uu____63094 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____63094 with
            | (uvs,t1) ->
                ((let uu____63114 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____63114
                  then
                    let uu____63119 =
                      let uu____63121 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____63121
                        (FStar_String.concat ", ")
                       in
                    let uu____63138 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____63119 uu____63138
                  else ());
                 (let uu____63143 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____63143 with
                  | (uvs1,t2) ->
                      let uu____63158 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____63158 with
                       | (args,uu____63182) ->
                           let uu____63203 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____63203 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____63308  ->
                                       fun uu____63309  ->
                                         match (uu____63308, uu____63309)
                                         with
                                         | ((x,uu____63331),(se,uu____63333))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____63349,tps,uu____63351,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____63363 =
                                                    let uu____63368 =
                                                      let uu____63369 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____63369.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____63368 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____63398 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____63398
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____63476
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____63495 -> ([], ty)
                                                     in
                                                  (match uu____63363 with
                                                   | (tps1,t3) ->
                                                       let uu___853_63504 =
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
                                                           (uu___853_63504.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_63504.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_63504.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_63504.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____63509 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____63516 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _63520  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _63520))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_63539  ->
                                                match uu___585_63539 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____63545,uu____63546,uu____63547,uu____63548,uu____63549);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____63550;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____63551;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____63552;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____63553;_}
                                                    -> (tc, uvs_universes)
                                                | uu____63566 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____63590  ->
                                           fun d  ->
                                             match uu____63590 with
                                             | (t3,uu____63599) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____63605,uu____63606,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____63617 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____63617
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_63618 = d
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
                                                          (uu___889_63618.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_63618.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_63618.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_63618.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____63622 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____63641 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____63641
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____63663 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____63663
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____63680 =
      let uu____63681 = FStar_Syntax_Subst.compress t  in
      uu____63681.FStar_Syntax_Syntax.n  in
    match uu____63680 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____63700 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____63706 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____63743 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____63792  ->
               match uu____63792 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____63836 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____63836  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____63743
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____64041 =
             let uu____64043 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____64043
              in
           debug_log env uu____64041);
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
           (let uu____64048 =
              let uu____64050 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____64050
               in
            debug_log env uu____64048);
           (let uu____64055 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____64055) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____64068 =
                  let uu____64069 = FStar_Syntax_Subst.compress btype1  in
                  uu____64069.FStar_Syntax_Syntax.n  in
                match uu____64068 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____64099 = try_get_fv t  in
                    (match uu____64099 with
                     | (fv,us) ->
                         let uu____64107 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____64107
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____64123  ->
                                 match uu____64123 with
                                 | (t1,uu____64132) ->
                                     let uu____64137 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____64137) args)
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
                          let uu____64172 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____64172
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____64176 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____64176
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
                            (fun uu____64203  ->
                               match uu____64203 with
                               | (b,uu____64212) ->
                                   let uu____64217 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____64217) sbs)
                           &&
                           ((let uu____64223 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____64223 with
                             | (uu____64229,return_type) ->
                                 let uu____64231 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____64231)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____64232 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____64236 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____64241) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____64249) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____64256,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____64315  ->
                          match uu____64315 with
                          | (p,uu____64328,t) ->
                              let bs =
                                let uu____64347 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____64347
                                 in
                              let uu____64356 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____64356 with
                               | (bs1,t1) ->
                                   let uu____64364 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____64364)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____64366,uu____64367)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____64410 ->
                    ((let uu____64412 =
                        let uu____64414 =
                          let uu____64416 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____64418 =
                            let uu____64420 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____64420  in
                          Prims.op_Hat uu____64416 uu____64418  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____64414
                         in
                      debug_log env uu____64412);
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
              (let uu____64433 =
                 let uu____64435 =
                   let uu____64437 =
                     let uu____64439 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____64439  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____64437  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____64435
                  in
               debug_log env uu____64433);
              (let uu____64443 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____64443 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____64462 =
                       let uu____64464 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____64464
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____64462
                      then
                        ((let uu____64468 =
                            let uu____64470 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____64470
                             in
                          debug_log env uu____64468);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____64481 =
                        already_unfolded ilid args unfolded env  in
                      if uu____64481
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____64492 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____64492  in
                         (let uu____64498 =
                            let uu____64500 =
                              let uu____64502 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____64502
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____64500
                             in
                          debug_log env uu____64498);
                         (let uu____64507 =
                            let uu____64508 = FStar_ST.op_Bang unfolded  in
                            let uu____64534 =
                              let uu____64541 =
                                let uu____64546 =
                                  let uu____64547 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____64547  in
                                (ilid, uu____64546)  in
                              [uu____64541]  in
                            FStar_List.append uu____64508 uu____64534  in
                          FStar_ST.op_Colon_Equals unfolded uu____64507);
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
                  (let uu____64646 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____64646 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____64669 ->
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
                         (let uu____64673 =
                            let uu____64675 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____64675
                             in
                          debug_log env uu____64673);
                         (let uu____64678 =
                            let uu____64679 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____64679.FStar_Syntax_Syntax.n  in
                          match uu____64678 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____64707 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____64707 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____64771 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____64771 dbs1
                                       in
                                    let c1 =
                                      let uu____64775 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____64775 c
                                       in
                                    let uu____64778 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____64778 with
                                     | (args1,uu____64813) ->
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
                                           let uu____64905 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____64905 c1
                                            in
                                         ((let uu____64915 =
                                             let uu____64917 =
                                               let uu____64919 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____64922 =
                                                 let uu____64924 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____64924
                                                  in
                                               Prims.op_Hat uu____64919
                                                 uu____64922
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____64917
                                              in
                                           debug_log env uu____64915);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____64938 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____64941 =
                                  let uu____64942 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____64942.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____64941
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
                   (let uu____64981 = try_get_fv t1  in
                    match uu____64981 with
                    | (fv,uu____64988) ->
                        let uu____64989 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____64989
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____65021 =
                      let uu____65023 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____65023
                       in
                    debug_log env uu____65021);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____65028 =
                      FStar_List.fold_left
                        (fun uu____65049  ->
                           fun b  ->
                             match uu____65049 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____65080 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____65084 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____65080, uu____65084))) (true, env)
                        sbs1
                       in
                    match uu____65028 with | (b,uu____65102) -> b))
              | uu____65105 ->
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
              let uu____65141 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____65141 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____65164 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____65167 =
                      let uu____65169 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____65169
                       in
                    debug_log env uu____65167);
                   (let uu____65172 =
                      let uu____65173 = FStar_Syntax_Subst.compress dt  in
                      uu____65173.FStar_Syntax_Syntax.n  in
                    match uu____65172 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____65177 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____65182) ->
                        let dbs1 =
                          let uu____65212 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____65212  in
                        let dbs2 =
                          let uu____65262 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____65262 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____65267 =
                            let uu____65269 =
                              let uu____65271 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____65271 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____65269
                             in
                          debug_log env uu____65267);
                         (let uu____65281 =
                            FStar_List.fold_left
                              (fun uu____65302  ->
                                 fun b  ->
                                   match uu____65302 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____65333 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____65337 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____65333, uu____65337)))
                              (true, env) dbs3
                             in
                          match uu____65281 with | (b,uu____65355) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____65358,uu____65359) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____65395 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____65418 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____65434,uu____65435,uu____65436) -> (lid, us, bs)
        | uu____65445 -> failwith "Impossible!"  in
      match uu____65418 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____65457 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____65457 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____65481 =
                 let uu____65484 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____65484  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____65498 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____65498
                      unfolded_inductives env2) uu____65481)
  
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
        (uu____65533,uu____65534,t,uu____65536,uu____65537,uu____65538) -> t
    | uu____65545 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____65562 =
         let uu____65564 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____65564 haseq_suffix  in
       uu____65562 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____65574 =
      let uu____65577 =
        let uu____65580 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____65580]  in
      FStar_List.append lid.FStar_Ident.ns uu____65577  in
    FStar_Ident.lid_of_ids uu____65574
  
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
          let uu____65626 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____65640,bs,t,uu____65643,uu____65644) ->
                (lid, bs, t)
            | uu____65653 -> failwith "Impossible!"  in
          match uu____65626 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____65676 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____65676 t  in
              let uu____65685 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____65685 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____65703 =
                       let uu____65704 = FStar_Syntax_Subst.compress t2  in
                       uu____65704.FStar_Syntax_Syntax.n  in
                     match uu____65703 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____65708) -> ibs
                     | uu____65729 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____65738 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____65739 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____65738 uu____65739
                      in
                   let ind1 =
                     let uu____65745 =
                       let uu____65750 =
                         FStar_List.map
                           (fun uu____65767  ->
                              match uu____65767 with
                              | (bv,aq) ->
                                  let uu____65786 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65786, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____65750  in
                     uu____65745 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____65792 =
                       let uu____65797 =
                         FStar_List.map
                           (fun uu____65814  ->
                              match uu____65814 with
                              | (bv,aq) ->
                                  let uu____65833 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65833, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____65797  in
                     uu____65792 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____65839 =
                       let uu____65844 =
                         let uu____65845 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____65845]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____65844
                        in
                     uu____65839 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____65894 =
                            let uu____65895 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____65895  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____65894) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____65908 =
                              let uu____65911 =
                                let uu____65916 =
                                  let uu____65917 =
                                    let uu____65926 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____65926
                                     in
                                  [uu____65917]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____65916
                                 in
                              uu____65911 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____65908)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_65949 = fml  in
                     let uu____65950 =
                       let uu____65951 =
                         let uu____65958 =
                           let uu____65959 =
                             let uu____65972 =
                               let uu____65983 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____65983]  in
                             [uu____65972]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____65959  in
                         (fml, uu____65958)  in
                       FStar_Syntax_Syntax.Tm_meta uu____65951  in
                     {
                       FStar_Syntax_Syntax.n = uu____65950;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_65949.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_65949.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66036 =
                              let uu____66041 =
                                let uu____66042 =
                                  let uu____66051 =
                                    let uu____66052 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66052
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66051  in
                                [uu____66042]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66041
                               in
                            uu____66036 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66105 =
                              let uu____66110 =
                                let uu____66111 =
                                  let uu____66120 =
                                    let uu____66121 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66121
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66120  in
                                [uu____66111]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66110
                               in
                            uu____66105 FStar_Pervasives_Native.None
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
          let uu____66196 =
            let uu____66197 = FStar_Syntax_Subst.compress dt1  in
            uu____66197.FStar_Syntax_Syntax.n  in
          match uu____66196 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____66201) ->
              let dbs1 =
                let uu____66231 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____66231  in
              let dbs2 =
                let uu____66281 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____66281 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____66296 =
                           let uu____66301 =
                             let uu____66302 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____66302]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____66301
                            in
                         uu____66296 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____66333 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____66333 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____66341 =
                       let uu____66346 =
                         let uu____66347 =
                           let uu____66356 =
                             let uu____66357 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____66357
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____66356  in
                         [uu____66347]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____66346
                        in
                     uu____66341 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____66404 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____66495,uu____66496,uu____66497,uu____66498,uu____66499)
                  -> lid
              | uu____66508 -> failwith "Impossible!"  in
            let uu____66510 = acc  in
            match uu____66510 with
            | (uu____66547,en,uu____66549,uu____66550) ->
                let uu____66571 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____66571 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____66608 = acc  in
                     (match uu____66608 with
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
                                     (uu____66683,uu____66684,uu____66685,t_lid,uu____66687,uu____66688)
                                     -> t_lid = lid
                                 | uu____66695 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____66710 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____66710)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____66713 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____66716 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____66713, uu____66716)))
  
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
          let uu____66774 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____66784,us,uu____66786,t,uu____66788,uu____66789) ->
                (us, t)
            | uu____66798 -> failwith "Impossible!"  in
          match uu____66774 with
          | (us,t) ->
              let uu____66808 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____66808 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____66834 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____66834 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____66912 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____66912 with
                           | (uu____66927,t1) ->
                               let uu____66949 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____66949
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____66954 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____66954 with
                          | (phi1,uu____66962) ->
                              ((let uu____66964 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____66964
                                then
                                  let uu____66967 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____66967
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____66985  ->
                                         match uu____66985 with
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
                let uu____67057 =
                  let uu____67058 = FStar_Syntax_Subst.compress t  in
                  uu____67058.FStar_Syntax_Syntax.n  in
                match uu____67057 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____67066) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____67103 = is_mutual t'  in
                    if uu____67103
                    then true
                    else
                      (let uu____67110 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____67110)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____67130) ->
                    is_mutual t'
                | uu____67135 -> false
              
              and exists_mutual uu___586_67137 =
                match uu___586_67137 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____67158 =
                let uu____67159 = FStar_Syntax_Subst.compress dt1  in
                uu____67159.FStar_Syntax_Syntax.n  in
              match uu____67158 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____67165) ->
                  let dbs1 =
                    let uu____67195 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____67195  in
                  let dbs2 =
                    let uu____67245 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____67245 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____67265 =
                               let uu____67270 =
                                 let uu____67271 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____67271]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____67270
                                in
                             uu____67265 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____67301 = is_mutual sort  in
                             if uu____67301
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
                           let uu____67314 =
                             let uu____67319 =
                               let uu____67320 =
                                 let uu____67329 =
                                   let uu____67330 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____67330 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____67329  in
                               [uu____67320]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____67319
                              in
                           uu____67314 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____67377 -> acc
  
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
              let uu____67427 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____67449,bs,t,uu____67452,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____67464 -> failwith "Impossible!"  in
              match uu____67427 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____67488 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____67488 t  in
                  let uu____67497 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____67497 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____67507 =
                           let uu____67508 = FStar_Syntax_Subst.compress t2
                              in
                           uu____67508.FStar_Syntax_Syntax.n  in
                         match uu____67507 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____67512) ->
                             ibs
                         | uu____67533 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____67542 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____67543 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____67542
                           uu____67543
                          in
                       let ind1 =
                         let uu____67549 =
                           let uu____67554 =
                             FStar_List.map
                               (fun uu____67571  ->
                                  match uu____67571 with
                                  | (bv,aq) ->
                                      let uu____67590 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67590, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____67554  in
                         uu____67549 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____67596 =
                           let uu____67601 =
                             FStar_List.map
                               (fun uu____67618  ->
                                  match uu____67618 with
                                  | (bv,aq) ->
                                      let uu____67637 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67637, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____67601  in
                         uu____67596 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____67643 =
                           let uu____67648 =
                             let uu____67649 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____67649]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____67648
                            in
                         uu____67643 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____67686,uu____67687,uu____67688,t_lid,uu____67690,uu____67691)
                                  -> t_lid = lid
                              | uu____67698 -> failwith "Impossible")
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
                         let uu___1460_67710 = fml  in
                         let uu____67711 =
                           let uu____67712 =
                             let uu____67719 =
                               let uu____67720 =
                                 let uu____67733 =
                                   let uu____67744 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____67744]  in
                                 [uu____67733]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____67720
                                in
                             (fml, uu____67719)  in
                           FStar_Syntax_Syntax.Tm_meta uu____67712  in
                         {
                           FStar_Syntax_Syntax.n = uu____67711;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_67710.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_67710.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67797 =
                                  let uu____67802 =
                                    let uu____67803 =
                                      let uu____67812 =
                                        let uu____67813 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67813
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67812
                                       in
                                    [uu____67803]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67802
                                   in
                                uu____67797 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67866 =
                                  let uu____67871 =
                                    let uu____67872 =
                                      let uu____67881 =
                                        let uu____67882 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67882
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67881
                                       in
                                    [uu____67872]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67871
                                   in
                                uu____67866 FStar_Pervasives_Native.None
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
                     (lid,uu____67974,uu____67975,uu____67976,uu____67977,uu____67978)
                     -> lid
                 | uu____67987 -> failwith "Impossible!") tcs
             in
          let uu____67989 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____68001,uu____68002,uu____68003,uu____68004) ->
                (lid, us)
            | uu____68013 -> failwith "Impossible!"  in
          match uu____67989 with
          | (lid,us) ->
              let uu____68023 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____68023 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____68050 =
                       let uu____68051 =
                         let uu____68058 = get_haseq_axiom_lid lid  in
                         (uu____68058, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____68051  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____68050;
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
          let uu____68112 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_68137  ->
                    match uu___587_68137 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____68139;
                        FStar_Syntax_Syntax.sigrng = uu____68140;
                        FStar_Syntax_Syntax.sigquals = uu____68141;
                        FStar_Syntax_Syntax.sigmeta = uu____68142;
                        FStar_Syntax_Syntax.sigattrs = uu____68143;_} -> true
                    | uu____68165 -> false))
             in
          match uu____68112 with
          | (tys,datas) ->
              ((let uu____68188 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_68199  ->
                          match uu___588_68199 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____68201;
                              FStar_Syntax_Syntax.sigrng = uu____68202;
                              FStar_Syntax_Syntax.sigquals = uu____68203;
                              FStar_Syntax_Syntax.sigmeta = uu____68204;
                              FStar_Syntax_Syntax.sigattrs = uu____68205;_}
                              -> false
                          | uu____68226 -> true))
                   in
                if uu____68188
                then
                  let uu____68229 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____68229
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____68244 =
                       let uu____68245 = FStar_List.hd tys  in
                       uu____68245.FStar_Syntax_Syntax.sigel  in
                     match uu____68244 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____68248,uvs,uu____68250,uu____68251,uu____68252,uu____68253)
                         -> uvs
                     | uu____68262 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____68267 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____68297 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____68297 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____68335,bs,t,l1,l2) ->
                                      let uu____68348 =
                                        let uu____68365 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____68366 =
                                          let uu____68367 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____68367 t
                                           in
                                        (lid, univs2, uu____68365,
                                          uu____68366, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____68348
                                  | uu____68380 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_68382 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_68382.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_68382.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_68382.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_68382.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____68392,t,lid_t,x,l) ->
                                      let uu____68403 =
                                        let uu____68419 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____68419, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____68403
                                  | uu____68423 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_68425 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_68425.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_68425.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_68425.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_68425.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____68426 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____68426, tys1, datas1))
                   in
                match uu____68267 with
                | (env1,tys1,datas1) ->
                    let uu____68452 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____68491  ->
                             match uu____68491 with
                             | (env2,all_tcs,g) ->
                                 let uu____68531 = tc_tycon env2 tc  in
                                 (match uu____68531 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____68558 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____68558
                                        then
                                          let uu____68561 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____68561
                                        else ());
                                       (let uu____68566 =
                                          let uu____68567 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____68567
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____68566))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____68452 with
                     | (env2,tcs,g) ->
                         let uu____68613 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____68635  ->
                                  match uu____68635 with
                                  | (datas2,g1) ->
                                      let uu____68654 =
                                        let uu____68659 = tc_data env2 tcs
                                           in
                                        uu____68659 se  in
                                      (match uu____68654 with
                                       | (data,g') ->
                                           let uu____68676 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____68676)))
                             datas1 ([], g)
                            in
                         (match uu____68613 with
                          | (datas2,g1) ->
                              let uu____68697 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____68719 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____68719, datas2))
                                 in
                              (match uu____68697 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____68751 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____68752 =
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
                                         uu____68751;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____68752
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____68778,uu____68779)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____68799 =
                                                    let uu____68805 =
                                                      let uu____68807 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____68809 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____68807
                                                        uu____68809
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____68805)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____68799
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____68813 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____68813 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____68829)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____68860 ->
                                                             let uu____68861
                                                               =
                                                               let uu____68868
                                                                 =
                                                                 let uu____68869
                                                                   =
                                                                   let uu____68884
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____68884)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____68869
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____68868
                                                                in
                                                             uu____68861
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
                                                       let uu____68906 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____68906
                                                        with
                                                        | (uu____68911,inferred)
                                                            ->
                                                            let uu____68913 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____68913
                                                             with
                                                             | (uu____68918,expected)
                                                                 ->
                                                                 let uu____68920
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____68920
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____68927 -> ()));
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
                          let uu____69038 =
                            let uu____69045 =
                              let uu____69046 =
                                let uu____69053 =
                                  let uu____69056 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____69056
                                   in
                                (uu____69053, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____69046  in
                            FStar_Syntax_Syntax.mk uu____69045  in
                          uu____69038 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____69090  ->
                                  match uu____69090 with
                                  | (x,imp) ->
                                      let uu____69109 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____69109, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____69113 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____69113  in
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
                               let uu____69136 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____69136
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____69138 =
                               let uu____69141 =
                                 let uu____69144 =
                                   let uu____69149 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____69150 =
                                     let uu____69151 =
                                       let uu____69160 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____69160
                                        in
                                     [uu____69151]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____69149
                                     uu____69150
                                    in
                                 uu____69144 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____69141  in
                             FStar_Syntax_Util.refine x uu____69138  in
                           let uu____69185 =
                             let uu___1671_69186 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_69186.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_69186.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____69185)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____69203 =
                          FStar_List.map
                            (fun uu____69227  ->
                               match uu____69227 with
                               | (x,uu____69241) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____69203 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____69300  ->
                                match uu____69300 with
                                | (x,uu____69314) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____69325 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____69325)
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
                               (let uu____69346 =
                                  let uu____69348 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____69348.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____69346)
                              in
                           let quals =
                             let uu____69352 =
                               FStar_List.filter
                                 (fun uu___589_69356  ->
                                    match uu___589_69356 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____69361 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____69352
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____69399 =
                                 let uu____69400 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____69400  in
                               FStar_Syntax_Syntax.mk_Total uu____69399  in
                             let uu____69401 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____69401
                              in
                           let decl =
                             let uu____69405 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____69405;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____69407 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____69407
                            then
                              let uu____69411 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____69411
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
                                             fun uu____69472  ->
                                               match uu____69472 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____69497 =
                                                       let uu____69500 =
                                                         let uu____69501 =
                                                           let uu____69508 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____69508,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____69501
                                                          in
                                                       pos uu____69500  in
                                                     (uu____69497, b)
                                                   else
                                                     (let uu____69516 =
                                                        let uu____69519 =
                                                          let uu____69520 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____69520
                                                           in
                                                        pos uu____69519  in
                                                      (uu____69516, b))))
                                      in
                                   let pat_true =
                                     let uu____69539 =
                                       let uu____69542 =
                                         let uu____69543 =
                                           let uu____69557 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____69557, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____69543
                                          in
                                       pos uu____69542  in
                                     (uu____69539,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____69592 =
                                       let uu____69595 =
                                         let uu____69596 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____69596
                                          in
                                       pos uu____69595  in
                                     (uu____69592,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____69610 =
                                     let uu____69617 =
                                       let uu____69618 =
                                         let uu____69641 =
                                           let uu____69658 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____69673 =
                                             let uu____69690 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____69690]  in
                                           uu____69658 :: uu____69673  in
                                         (arg_exp, uu____69641)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____69618
                                        in
                                     FStar_Syntax_Syntax.mk uu____69617  in
                                   uu____69610 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____69766 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____69766
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
                                let uu____69788 =
                                  let uu____69793 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____69793  in
                                let uu____69794 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____69788
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____69794 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____69800 =
                                  let uu____69801 =
                                    let uu____69808 =
                                      let uu____69811 =
                                        let uu____69812 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____69812
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____69811]  in
                                    ((false, [lb]), uu____69808)  in
                                  FStar_Syntax_Syntax.Sig_let uu____69801  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____69800;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____69826 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____69826
                               then
                                 let uu____69830 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____69830
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
                                fun uu____69903  ->
                                  match uu____69903 with
                                  | (a,uu____69912) ->
                                      let uu____69917 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____69917 with
                                       | (field_name,uu____69923) ->
                                           let field_proj_tm =
                                             let uu____69925 =
                                               let uu____69926 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____69926
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____69925 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____69952 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____69994  ->
                                    match uu____69994 with
                                    | (x,uu____70005) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____70011 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____70011 with
                                         | (field_name,uu____70019) ->
                                             let t =
                                               let uu____70023 =
                                                 let uu____70024 =
                                                   let uu____70027 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____70027
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____70024
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____70023
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____70033 =
                                                    let uu____70035 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____70035.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____70033)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____70054 =
                                                   FStar_List.filter
                                                     (fun uu___590_70058  ->
                                                        match uu___590_70058
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____70061 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____70054
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_70076  ->
                                                         match uu___591_70076
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____70082 ->
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
                                               let uu____70093 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____70093;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____70095 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____70095
                                               then
                                                 let uu____70099 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____70099
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
                                                           fun uu____70153 
                                                             ->
                                                             match uu____70153
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
                                                                   let uu____70179
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____70179,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____70195
                                                                    =
                                                                    let uu____70198
                                                                    =
                                                                    let uu____70199
                                                                    =
                                                                    let uu____70206
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____70206,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____70199
                                                                     in
                                                                    pos
                                                                    uu____70198
                                                                     in
                                                                    (uu____70195,
                                                                    b))
                                                                   else
                                                                    (let uu____70214
                                                                    =
                                                                    let uu____70217
                                                                    =
                                                                    let uu____70218
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____70218
                                                                     in
                                                                    pos
                                                                    uu____70217
                                                                     in
                                                                    (uu____70214,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____70237 =
                                                     let uu____70240 =
                                                       let uu____70241 =
                                                         let uu____70255 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____70255,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____70241
                                                        in
                                                     pos uu____70240  in
                                                   let uu____70265 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____70237,
                                                     FStar_Pervasives_Native.None,
                                                     uu____70265)
                                                    in
                                                 let body =
                                                   let uu____70281 =
                                                     let uu____70288 =
                                                       let uu____70289 =
                                                         let uu____70312 =
                                                           let uu____70329 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____70329]  in
                                                         (arg_exp,
                                                           uu____70312)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____70289
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____70288
                                                      in
                                                   uu____70281
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____70394 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____70394
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
                                                   let uu____70413 =
                                                     let uu____70418 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____70418
                                                      in
                                                   let uu____70419 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____70413;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____70419;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____70425 =
                                                     let uu____70426 =
                                                       let uu____70433 =
                                                         let uu____70436 =
                                                           let uu____70437 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____70437
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____70436]  in
                                                       ((false, [lb]),
                                                         uu____70433)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____70426
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____70425;
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
                                                 (let uu____70451 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____70451
                                                  then
                                                    let uu____70455 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____70455
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____69952 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____70509) when
              let uu____70516 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____70516 ->
              let uu____70518 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____70518 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____70540 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____70540 with
                    | (formals,uu____70558) ->
                        let uu____70579 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____70614 =
                                   let uu____70616 =
                                     let uu____70617 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____70617  in
                                   FStar_Ident.lid_equals typ_lid uu____70616
                                    in
                                 if uu____70614
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____70639,uvs',tps,typ0,uu____70643,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____70663 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____70712 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____70712
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____70579 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____70750 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____70750 with
                              | (indices,uu____70768) ->
                                  let refine_domain =
                                    let uu____70791 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_70798  ->
                                              match uu___592_70798 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____70800 -> true
                                              | uu____70810 -> false))
                                       in
                                    if uu____70791
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_70825 =
                                      match uu___593_70825 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____70828,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____70840 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____70841 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____70841 with
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
                                    let uu____70854 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____70854 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____70937  ->
                                               fun uu____70938  ->
                                                 match (uu____70937,
                                                         uu____70938)
                                                 with
                                                 | ((x,uu____70964),(x',uu____70966))
                                                     ->
                                                     let uu____70987 =
                                                       let uu____70994 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____70994)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____70987) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____70999 -> []
  