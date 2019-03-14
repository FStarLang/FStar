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
          let uu____61419 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____61419 with
           | (usubst,uvs1) ->
               let uu____61446 =
                 let uu____61453 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____61454 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____61455 =
                   let uu____61456 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____61456 k  in
                 (uu____61453, uu____61454, uu____61455)  in
               (match uu____61446 with
                | (env1,tps1,k1) ->
                    let uu____61476 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____61476 with
                     | (tps2,k2) ->
                         let uu____61491 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____61491 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____61512 =
                                let uu____61531 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____61531 with
                                | (k3,uu____61557,g) ->
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
                                    let uu____61560 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____61575 =
                                      let uu____61576 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____61576
                                       in
                                    (uu____61560, uu____61575)
                                 in
                              (match uu____61512 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____61639 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____61639
                                      in
                                   let uu____61642 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____61642 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____61660 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____61660))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____61667 =
                                              let uu____61673 =
                                                let uu____61675 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____61677 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____61675 uu____61677
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____61673)
                                               in
                                            FStar_Errors.raise_error
                                              uu____61667
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
                                            let uu____61690 =
                                              let uu____61699 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____61716 =
                                                let uu____61725 =
                                                  let uu____61738 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____61738
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____61725
                                                 in
                                              FStar_List.append uu____61699
                                                uu____61716
                                               in
                                            let uu____61761 =
                                              let uu____61764 =
                                                let uu____61765 =
                                                  let uu____61770 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____61770
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____61765
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____61764
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____61690 uu____61761
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____61787 =
                                            let uu____61792 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____61793 =
                                              let uu____61794 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____61794 k4
                                               in
                                            (uu____61792, uu____61793)  in
                                          match uu____61787 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____61814 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____61814,
                                                (let uu___646_61820 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_61820.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_61820.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_61820.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_61820.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____61825 -> failwith "impossible"
  
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
            let uu____61889 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____61889 with
             | (usubst,_uvs1) ->
                 let uu____61912 =
                   let uu____61917 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____61918 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____61917, uu____61918)  in
                 (match uu____61912 with
                  | (env1,t1) ->
                      let uu____61925 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____61964  ->
                               match uu____61964 with
                               | (se1,u_tc) ->
                                   let uu____61979 =
                                     let uu____61981 =
                                       let uu____61982 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____61982  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____61981
                                      in
                                   if uu____61979
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____62002,uu____62003,tps,uu____62005,uu____62006,uu____62007)
                                          ->
                                          let tps1 =
                                            let uu____62017 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____62017
                                              (FStar_List.map
                                                 (fun uu____62057  ->
                                                    match uu____62057 with
                                                    | (x,uu____62071) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____62079 =
                                            let uu____62086 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____62086, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____62079
                                      | uu____62093 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____62136 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____62136
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____61925 with
                       | (env2,tps,u_tc) ->
                           let uu____62168 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____62184 =
                               let uu____62185 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____62185.FStar_Syntax_Syntax.n  in
                             match uu____62184 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____62224 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____62224 with
                                  | (uu____62265,bs') ->
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
                                                fun uu____62336  ->
                                                  match uu____62336 with
                                                  | (x,uu____62345) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____62352 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____62352)
                             | uu____62353 -> ([], t2)  in
                           (match uu____62168 with
                            | (arguments,result) ->
                                ((let uu____62397 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____62397
                                  then
                                    let uu____62400 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____62402 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____62405 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____62400 uu____62402 uu____62405
                                  else ());
                                 (let uu____62410 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____62410 with
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
                                      let uu____62428 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____62428 with
                                       | (result1,res_lcomp) ->
                                           let uu____62439 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____62439 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____62497 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____62497
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____62579  ->
                                                      fun uu____62580  ->
                                                        match (uu____62579,
                                                                uu____62580)
                                                        with
                                                        | ((bv,uu____62610),
                                                           (t2,uu____62612))
                                                            ->
                                                            let uu____62639 =
                                                              let uu____62640
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____62640.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____62639
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____62644 ->
                                                                 let uu____62645
                                                                   =
                                                                   let uu____62651
                                                                    =
                                                                    let uu____62653
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____62655
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____62653
                                                                    uu____62655
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____62651)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____62645
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____62660 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____62660
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____62662 =
                                                     let uu____62663 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____62663.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____62662 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____62666 -> ()
                                                   | uu____62667 ->
                                                       let uu____62668 =
                                                         let uu____62674 =
                                                           let uu____62676 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____62678 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____62676
                                                             uu____62678
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____62674)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____62668
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____62683 =
                                                       let uu____62684 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____62684.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____62683 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____62688;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____62689;_},tuvs)
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
                                                                    let uu____62703
                                                                    =
                                                                    let uu____62704
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____62705
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
                                                                    uu____62704
                                                                    uu____62705
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62703)
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
                                                     | uu____62711 ->
                                                         let uu____62712 =
                                                           let uu____62718 =
                                                             let uu____62720
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____62722
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____62720
                                                               uu____62722
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____62718)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____62712
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____62740  ->
                                                            fun u_x  ->
                                                              match uu____62740
                                                              with
                                                              | (x,uu____62749)
                                                                  ->
                                                                  let uu____62754
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62754)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____62758 =
                                                       let uu____62767 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____62807 
                                                                 ->
                                                                 match uu____62807
                                                                 with
                                                                 | (x,uu____62821)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____62767
                                                         arguments1
                                                        in
                                                     let uu____62835 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____62758
                                                       uu____62835
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_62840 = se
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
                                                         (uu___768_62840.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_62840.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_62840.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_62840.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____62844 -> failwith "impossible"
  
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
            let uu___776_62911 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_62911.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_62911.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_62911.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____62921 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____62921
           then
             let uu____62926 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____62926
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____62969  ->
                     match uu____62969 with
                     | (se,uu____62975) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____62976,uu____62977,tps,k,uu____62980,uu____62981)
                              ->
                              let uu____62990 =
                                let uu____62991 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____62991
                                 in
                              FStar_Syntax_Syntax.null_binder uu____62990
                          | uu____62996 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____63025,uu____63026,t,uu____63028,uu____63029,uu____63030)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____63037 -> failwith "Impossible"))
              in
           let t =
             let uu____63042 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____63042
              in
           (let uu____63052 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____63052
            then
              let uu____63057 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____63057
            else ());
           (let uu____63062 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____63062 with
            | (uvs,t1) ->
                ((let uu____63082 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____63082
                  then
                    let uu____63087 =
                      let uu____63089 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____63089
                        (FStar_String.concat ", ")
                       in
                    let uu____63106 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____63087 uu____63106
                  else ());
                 (let uu____63111 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____63111 with
                  | (uvs1,t2) ->
                      let uu____63126 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____63126 with
                       | (args,uu____63150) ->
                           let uu____63171 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____63171 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____63276  ->
                                       fun uu____63277  ->
                                         match (uu____63276, uu____63277)
                                         with
                                         | ((x,uu____63299),(se,uu____63301))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____63317,tps,uu____63319,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____63331 =
                                                    let uu____63336 =
                                                      let uu____63337 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____63337.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____63336 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____63366 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____63366
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____63444
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____63463 -> ([], ty)
                                                     in
                                                  (match uu____63331 with
                                                   | (tps1,t3) ->
                                                       let uu___853_63472 =
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
                                                           (uu___853_63472.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_63472.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_63472.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_63472.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____63477 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____63484 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _63488  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _63488))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_63507  ->
                                                match uu___585_63507 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____63513,uu____63514,uu____63515,uu____63516,uu____63517);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____63518;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____63519;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____63520;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____63521;_}
                                                    -> (tc, uvs_universes)
                                                | uu____63534 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____63558  ->
                                           fun d  ->
                                             match uu____63558 with
                                             | (t3,uu____63567) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____63573,uu____63574,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____63585 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____63585
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_63586 = d
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
                                                          (uu___889_63586.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_63586.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_63586.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_63586.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____63590 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____63609 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____63609
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____63631 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____63631
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____63648 =
      let uu____63649 = FStar_Syntax_Subst.compress t  in
      uu____63649.FStar_Syntax_Syntax.n  in
    match uu____63648 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____63668 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____63674 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____63711 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____63760  ->
               match uu____63760 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____63804 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____63804  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____63711
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____64009 =
             let uu____64011 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____64011
              in
           debug_log env uu____64009);
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
           (let uu____64016 =
              let uu____64018 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____64018
               in
            debug_log env uu____64016);
           (let uu____64023 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____64023) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____64036 =
                  let uu____64037 = FStar_Syntax_Subst.compress btype1  in
                  uu____64037.FStar_Syntax_Syntax.n  in
                match uu____64036 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____64067 = try_get_fv t  in
                    (match uu____64067 with
                     | (fv,us) ->
                         let uu____64075 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____64075
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____64091  ->
                                 match uu____64091 with
                                 | (t1,uu____64100) ->
                                     let uu____64105 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____64105) args)
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
                          let uu____64140 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____64140
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____64144 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____64144
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
                            (fun uu____64171  ->
                               match uu____64171 with
                               | (b,uu____64180) ->
                                   let uu____64185 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____64185) sbs)
                           &&
                           ((let uu____64191 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____64191 with
                             | (uu____64197,return_type) ->
                                 let uu____64199 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____64199)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____64200 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____64204 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____64209) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____64217) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____64224,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____64283  ->
                          match uu____64283 with
                          | (p,uu____64296,t) ->
                              let bs =
                                let uu____64315 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____64315
                                 in
                              let uu____64324 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____64324 with
                               | (bs1,t1) ->
                                   let uu____64332 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____64332)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____64334,uu____64335)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____64378 ->
                    ((let uu____64380 =
                        let uu____64382 =
                          let uu____64384 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____64386 =
                            let uu____64388 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____64388  in
                          Prims.op_Hat uu____64384 uu____64386  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____64382
                         in
                      debug_log env uu____64380);
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
              (let uu____64401 =
                 let uu____64403 =
                   let uu____64405 =
                     let uu____64407 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____64407  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____64405  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____64403
                  in
               debug_log env uu____64401);
              (let uu____64411 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____64411 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____64430 =
                       let uu____64432 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____64432
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____64430
                      then
                        ((let uu____64436 =
                            let uu____64438 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____64438
                             in
                          debug_log env uu____64436);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____64449 =
                        already_unfolded ilid args unfolded env  in
                      if uu____64449
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____64460 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____64460  in
                         (let uu____64466 =
                            let uu____64468 =
                              let uu____64470 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____64470
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____64468
                             in
                          debug_log env uu____64466);
                         (let uu____64475 =
                            let uu____64476 = FStar_ST.op_Bang unfolded  in
                            let uu____64502 =
                              let uu____64509 =
                                let uu____64514 =
                                  let uu____64515 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____64515  in
                                (ilid, uu____64514)  in
                              [uu____64509]  in
                            FStar_List.append uu____64476 uu____64502  in
                          FStar_ST.op_Colon_Equals unfolded uu____64475);
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
                  (let uu____64614 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____64614 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____64637 ->
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
                         (let uu____64641 =
                            let uu____64643 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____64643
                             in
                          debug_log env uu____64641);
                         (let uu____64646 =
                            let uu____64647 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____64647.FStar_Syntax_Syntax.n  in
                          match uu____64646 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____64675 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____64675 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____64739 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____64739 dbs1
                                       in
                                    let c1 =
                                      let uu____64743 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____64743 c
                                       in
                                    let uu____64746 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____64746 with
                                     | (args1,uu____64781) ->
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
                                           let uu____64873 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____64873 c1
                                            in
                                         ((let uu____64883 =
                                             let uu____64885 =
                                               let uu____64887 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____64890 =
                                                 let uu____64892 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____64892
                                                  in
                                               Prims.op_Hat uu____64887
                                                 uu____64890
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____64885
                                              in
                                           debug_log env uu____64883);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____64906 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____64909 =
                                  let uu____64910 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____64910.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____64909
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
                   (let uu____64949 = try_get_fv t1  in
                    match uu____64949 with
                    | (fv,uu____64956) ->
                        let uu____64957 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____64957
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____64989 =
                      let uu____64991 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____64991
                       in
                    debug_log env uu____64989);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____64996 =
                      FStar_List.fold_left
                        (fun uu____65017  ->
                           fun b  ->
                             match uu____65017 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____65048 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____65052 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____65048, uu____65052))) (true, env)
                        sbs1
                       in
                    match uu____64996 with | (b,uu____65070) -> b))
              | uu____65073 ->
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
              let uu____65109 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____65109 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____65132 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____65135 =
                      let uu____65137 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____65137
                       in
                    debug_log env uu____65135);
                   (let uu____65140 =
                      let uu____65141 = FStar_Syntax_Subst.compress dt  in
                      uu____65141.FStar_Syntax_Syntax.n  in
                    match uu____65140 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____65145 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____65150) ->
                        let dbs1 =
                          let uu____65180 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____65180  in
                        let dbs2 =
                          let uu____65230 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____65230 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____65235 =
                            let uu____65237 =
                              let uu____65239 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____65239 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____65237
                             in
                          debug_log env uu____65235);
                         (let uu____65249 =
                            FStar_List.fold_left
                              (fun uu____65270  ->
                                 fun b  ->
                                   match uu____65270 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____65301 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____65305 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____65301, uu____65305)))
                              (true, env) dbs3
                             in
                          match uu____65249 with | (b,uu____65323) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____65326,uu____65327) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____65363 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____65386 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____65402,uu____65403,uu____65404) -> (lid, us, bs)
        | uu____65413 -> failwith "Impossible!"  in
      match uu____65386 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____65425 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____65425 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____65449 =
                 let uu____65452 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____65452  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____65466 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____65466
                      unfolded_inductives env2) uu____65449)
  
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
        (uu____65501,uu____65502,t,uu____65504,uu____65505,uu____65506) -> t
    | uu____65513 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____65530 =
         let uu____65532 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____65532 haseq_suffix  in
       uu____65530 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____65542 =
      let uu____65545 =
        let uu____65548 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____65548]  in
      FStar_List.append lid.FStar_Ident.ns uu____65545  in
    FStar_Ident.lid_of_ids uu____65542
  
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
          let uu____65594 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____65608,bs,t,uu____65611,uu____65612) ->
                (lid, bs, t)
            | uu____65621 -> failwith "Impossible!"  in
          match uu____65594 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____65644 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____65644 t  in
              let uu____65653 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____65653 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____65671 =
                       let uu____65672 = FStar_Syntax_Subst.compress t2  in
                       uu____65672.FStar_Syntax_Syntax.n  in
                     match uu____65671 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____65676) -> ibs
                     | uu____65697 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____65706 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____65707 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____65706 uu____65707
                      in
                   let ind1 =
                     let uu____65713 =
                       let uu____65718 =
                         FStar_List.map
                           (fun uu____65735  ->
                              match uu____65735 with
                              | (bv,aq) ->
                                  let uu____65754 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65754, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____65718  in
                     uu____65713 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____65760 =
                       let uu____65765 =
                         FStar_List.map
                           (fun uu____65782  ->
                              match uu____65782 with
                              | (bv,aq) ->
                                  let uu____65801 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65801, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____65765  in
                     uu____65760 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____65807 =
                       let uu____65812 =
                         let uu____65813 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____65813]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____65812
                        in
                     uu____65807 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____65862 =
                            let uu____65863 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____65863  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____65862) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____65876 =
                              let uu____65879 =
                                let uu____65884 =
                                  let uu____65885 =
                                    let uu____65894 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____65894
                                     in
                                  [uu____65885]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____65884
                                 in
                              uu____65879 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____65876)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_65917 = fml  in
                     let uu____65918 =
                       let uu____65919 =
                         let uu____65926 =
                           let uu____65927 =
                             let uu____65940 =
                               let uu____65951 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____65951]  in
                             [uu____65940]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____65927  in
                         (fml, uu____65926)  in
                       FStar_Syntax_Syntax.Tm_meta uu____65919  in
                     {
                       FStar_Syntax_Syntax.n = uu____65918;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_65917.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_65917.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66004 =
                              let uu____66009 =
                                let uu____66010 =
                                  let uu____66019 =
                                    let uu____66020 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66020
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66019  in
                                [uu____66010]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66009
                               in
                            uu____66004 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66073 =
                              let uu____66078 =
                                let uu____66079 =
                                  let uu____66088 =
                                    let uu____66089 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66089
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66088  in
                                [uu____66079]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66078
                               in
                            uu____66073 FStar_Pervasives_Native.None
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
          let uu____66164 =
            let uu____66165 = FStar_Syntax_Subst.compress dt1  in
            uu____66165.FStar_Syntax_Syntax.n  in
          match uu____66164 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____66169) ->
              let dbs1 =
                let uu____66199 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____66199  in
              let dbs2 =
                let uu____66249 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____66249 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____66264 =
                           let uu____66269 =
                             let uu____66270 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____66270]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____66269
                            in
                         uu____66264 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____66301 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____66301 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____66309 =
                       let uu____66314 =
                         let uu____66315 =
                           let uu____66324 =
                             let uu____66325 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____66325
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____66324  in
                         [uu____66315]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____66314
                        in
                     uu____66309 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____66372 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____66463,uu____66464,uu____66465,uu____66466,uu____66467)
                  -> lid
              | uu____66476 -> failwith "Impossible!"  in
            let uu____66478 = acc  in
            match uu____66478 with
            | (uu____66515,en,uu____66517,uu____66518) ->
                let uu____66539 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____66539 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____66576 = acc  in
                     (match uu____66576 with
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
                                     (uu____66651,uu____66652,uu____66653,t_lid,uu____66655,uu____66656)
                                     -> t_lid = lid
                                 | uu____66663 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____66678 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____66678)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____66681 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____66684 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____66681, uu____66684)))
  
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
          let uu____66742 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____66752,us,uu____66754,t,uu____66756,uu____66757) ->
                (us, t)
            | uu____66766 -> failwith "Impossible!"  in
          match uu____66742 with
          | (us,t) ->
              let uu____66776 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____66776 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____66802 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____66802 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____66880 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____66880 with
                           | (uu____66895,t1) ->
                               let uu____66917 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____66917
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____66922 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____66922 with
                          | (phi1,uu____66930) ->
                              ((let uu____66932 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____66932
                                then
                                  let uu____66935 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____66935
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____66953  ->
                                         match uu____66953 with
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
                let uu____67025 =
                  let uu____67026 = FStar_Syntax_Subst.compress t  in
                  uu____67026.FStar_Syntax_Syntax.n  in
                match uu____67025 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____67034) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____67071 = is_mutual t'  in
                    if uu____67071
                    then true
                    else
                      (let uu____67078 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____67078)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____67098) ->
                    is_mutual t'
                | uu____67103 -> false
              
              and exists_mutual uu___586_67105 =
                match uu___586_67105 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____67126 =
                let uu____67127 = FStar_Syntax_Subst.compress dt1  in
                uu____67127.FStar_Syntax_Syntax.n  in
              match uu____67126 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____67133) ->
                  let dbs1 =
                    let uu____67163 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____67163  in
                  let dbs2 =
                    let uu____67213 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____67213 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____67233 =
                               let uu____67238 =
                                 let uu____67239 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____67239]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____67238
                                in
                             uu____67233 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____67269 = is_mutual sort  in
                             if uu____67269
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
                           let uu____67282 =
                             let uu____67287 =
                               let uu____67288 =
                                 let uu____67297 =
                                   let uu____67298 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____67298 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____67297  in
                               [uu____67288]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____67287
                              in
                           uu____67282 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____67345 -> acc
  
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
              let uu____67395 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____67417,bs,t,uu____67420,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____67432 -> failwith "Impossible!"  in
              match uu____67395 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____67456 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____67456 t  in
                  let uu____67465 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____67465 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____67475 =
                           let uu____67476 = FStar_Syntax_Subst.compress t2
                              in
                           uu____67476.FStar_Syntax_Syntax.n  in
                         match uu____67475 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____67480) ->
                             ibs
                         | uu____67501 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____67510 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____67511 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____67510
                           uu____67511
                          in
                       let ind1 =
                         let uu____67517 =
                           let uu____67522 =
                             FStar_List.map
                               (fun uu____67539  ->
                                  match uu____67539 with
                                  | (bv,aq) ->
                                      let uu____67558 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67558, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____67522  in
                         uu____67517 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____67564 =
                           let uu____67569 =
                             FStar_List.map
                               (fun uu____67586  ->
                                  match uu____67586 with
                                  | (bv,aq) ->
                                      let uu____67605 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67605, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____67569  in
                         uu____67564 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____67611 =
                           let uu____67616 =
                             let uu____67617 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____67617]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____67616
                            in
                         uu____67611 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____67654,uu____67655,uu____67656,t_lid,uu____67658,uu____67659)
                                  -> t_lid = lid
                              | uu____67666 -> failwith "Impossible")
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
                         let uu___1460_67678 = fml  in
                         let uu____67679 =
                           let uu____67680 =
                             let uu____67687 =
                               let uu____67688 =
                                 let uu____67701 =
                                   let uu____67712 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____67712]  in
                                 [uu____67701]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____67688
                                in
                             (fml, uu____67687)  in
                           FStar_Syntax_Syntax.Tm_meta uu____67680  in
                         {
                           FStar_Syntax_Syntax.n = uu____67679;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_67678.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_67678.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67765 =
                                  let uu____67770 =
                                    let uu____67771 =
                                      let uu____67780 =
                                        let uu____67781 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67781
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67780
                                       in
                                    [uu____67771]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67770
                                   in
                                uu____67765 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67834 =
                                  let uu____67839 =
                                    let uu____67840 =
                                      let uu____67849 =
                                        let uu____67850 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67850
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67849
                                       in
                                    [uu____67840]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67839
                                   in
                                uu____67834 FStar_Pervasives_Native.None
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
                     (lid,uu____67942,uu____67943,uu____67944,uu____67945,uu____67946)
                     -> lid
                 | uu____67955 -> failwith "Impossible!") tcs
             in
          let uu____67957 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____67969,uu____67970,uu____67971,uu____67972) ->
                (lid, us)
            | uu____67981 -> failwith "Impossible!"  in
          match uu____67957 with
          | (lid,us) ->
              let uu____67991 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____67991 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____68018 =
                       let uu____68019 =
                         let uu____68026 = get_haseq_axiom_lid lid  in
                         (uu____68026, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____68019  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____68018;
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
          let uu____68080 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_68105  ->
                    match uu___587_68105 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____68107;
                        FStar_Syntax_Syntax.sigrng = uu____68108;
                        FStar_Syntax_Syntax.sigquals = uu____68109;
                        FStar_Syntax_Syntax.sigmeta = uu____68110;
                        FStar_Syntax_Syntax.sigattrs = uu____68111;_} -> true
                    | uu____68133 -> false))
             in
          match uu____68080 with
          | (tys,datas) ->
              ((let uu____68156 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_68167  ->
                          match uu___588_68167 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____68169;
                              FStar_Syntax_Syntax.sigrng = uu____68170;
                              FStar_Syntax_Syntax.sigquals = uu____68171;
                              FStar_Syntax_Syntax.sigmeta = uu____68172;
                              FStar_Syntax_Syntax.sigattrs = uu____68173;_}
                              -> false
                          | uu____68194 -> true))
                   in
                if uu____68156
                then
                  let uu____68197 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____68197
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____68212 =
                       let uu____68213 = FStar_List.hd tys  in
                       uu____68213.FStar_Syntax_Syntax.sigel  in
                     match uu____68212 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____68216,uvs,uu____68218,uu____68219,uu____68220,uu____68221)
                         -> uvs
                     | uu____68230 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____68235 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____68265 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____68265 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____68303,bs,t,l1,l2) ->
                                      let uu____68316 =
                                        let uu____68333 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____68334 =
                                          let uu____68335 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____68335 t
                                           in
                                        (lid, univs2, uu____68333,
                                          uu____68334, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____68316
                                  | uu____68348 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_68350 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_68350.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_68350.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_68350.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_68350.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____68360,t,lid_t,x,l) ->
                                      let uu____68371 =
                                        let uu____68387 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____68387, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____68371
                                  | uu____68391 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_68393 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_68393.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_68393.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_68393.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_68393.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____68394 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____68394, tys1, datas1))
                   in
                match uu____68235 with
                | (env1,tys1,datas1) ->
                    let uu____68420 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____68459  ->
                             match uu____68459 with
                             | (env2,all_tcs,g) ->
                                 let uu____68499 = tc_tycon env2 tc  in
                                 (match uu____68499 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____68526 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____68526
                                        then
                                          let uu____68529 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____68529
                                        else ());
                                       (let uu____68534 =
                                          let uu____68535 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____68535
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____68534))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____68420 with
                     | (env2,tcs,g) ->
                         let uu____68581 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____68603  ->
                                  match uu____68603 with
                                  | (datas2,g1) ->
                                      let uu____68622 =
                                        let uu____68627 = tc_data env2 tcs
                                           in
                                        uu____68627 se  in
                                      (match uu____68622 with
                                       | (data,g') ->
                                           let uu____68644 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____68644)))
                             datas1 ([], g)
                            in
                         (match uu____68581 with
                          | (datas2,g1) ->
                              let uu____68665 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____68687 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____68687, datas2))
                                 in
                              (match uu____68665 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____68719 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____68720 =
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
                                         uu____68719;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____68720
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____68746,uu____68747)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____68767 =
                                                    let uu____68773 =
                                                      let uu____68775 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____68777 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____68775
                                                        uu____68777
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____68773)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____68767
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____68781 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____68781 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____68797)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____68828 ->
                                                             let uu____68829
                                                               =
                                                               let uu____68836
                                                                 =
                                                                 let uu____68837
                                                                   =
                                                                   let uu____68852
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____68852)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____68837
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____68836
                                                                in
                                                             uu____68829
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
                                                       let uu____68874 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____68874
                                                        with
                                                        | (uu____68879,inferred)
                                                            ->
                                                            let uu____68881 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____68881
                                                             with
                                                             | (uu____68886,expected)
                                                                 ->
                                                                 let uu____68888
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____68888
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____68895 -> ()));
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
                          let uu____69006 =
                            let uu____69013 =
                              let uu____69014 =
                                let uu____69021 =
                                  let uu____69024 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____69024
                                   in
                                (uu____69021, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____69014  in
                            FStar_Syntax_Syntax.mk uu____69013  in
                          uu____69006 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____69058  ->
                                  match uu____69058 with
                                  | (x,imp) ->
                                      let uu____69077 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____69077, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____69081 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____69081  in
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
                               let uu____69104 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____69104
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____69106 =
                               let uu____69109 =
                                 let uu____69112 =
                                   let uu____69117 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____69118 =
                                     let uu____69119 =
                                       let uu____69128 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____69128
                                        in
                                     [uu____69119]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____69117
                                     uu____69118
                                    in
                                 uu____69112 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____69109  in
                             FStar_Syntax_Util.refine x uu____69106  in
                           let uu____69153 =
                             let uu___1671_69154 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_69154.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_69154.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____69153)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____69171 =
                          FStar_List.map
                            (fun uu____69195  ->
                               match uu____69195 with
                               | (x,uu____69209) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____69171 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____69268  ->
                                match uu____69268 with
                                | (x,uu____69282) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____69293 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____69293)
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
                               (let uu____69314 =
                                  let uu____69316 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____69316.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____69314)
                              in
                           let quals =
                             let uu____69320 =
                               FStar_List.filter
                                 (fun uu___589_69324  ->
                                    match uu___589_69324 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____69329 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____69320
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____69367 =
                                 let uu____69368 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____69368  in
                               FStar_Syntax_Syntax.mk_Total uu____69367  in
                             let uu____69369 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____69369
                              in
                           let decl =
                             let uu____69373 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____69373;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____69375 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____69375
                            then
                              let uu____69379 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____69379
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
                                             fun uu____69440  ->
                                               match uu____69440 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____69465 =
                                                       let uu____69468 =
                                                         let uu____69469 =
                                                           let uu____69476 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____69476,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____69469
                                                          in
                                                       pos uu____69468  in
                                                     (uu____69465, b)
                                                   else
                                                     (let uu____69484 =
                                                        let uu____69487 =
                                                          let uu____69488 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____69488
                                                           in
                                                        pos uu____69487  in
                                                      (uu____69484, b))))
                                      in
                                   let pat_true =
                                     let uu____69507 =
                                       let uu____69510 =
                                         let uu____69511 =
                                           let uu____69525 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____69525, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____69511
                                          in
                                       pos uu____69510  in
                                     (uu____69507,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____69560 =
                                       let uu____69563 =
                                         let uu____69564 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____69564
                                          in
                                       pos uu____69563  in
                                     (uu____69560,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____69578 =
                                     let uu____69585 =
                                       let uu____69586 =
                                         let uu____69609 =
                                           let uu____69626 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____69641 =
                                             let uu____69658 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____69658]  in
                                           uu____69626 :: uu____69641  in
                                         (arg_exp, uu____69609)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____69586
                                        in
                                     FStar_Syntax_Syntax.mk uu____69585  in
                                   uu____69578 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____69734 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____69734
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
                                let uu____69756 =
                                  let uu____69761 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____69761  in
                                let uu____69762 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____69756
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____69762 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____69768 =
                                  let uu____69769 =
                                    let uu____69776 =
                                      let uu____69779 =
                                        let uu____69780 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____69780
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____69779]  in
                                    ((false, [lb]), uu____69776)  in
                                  FStar_Syntax_Syntax.Sig_let uu____69769  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____69768;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____69794 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____69794
                               then
                                 let uu____69798 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____69798
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
                                fun uu____69871  ->
                                  match uu____69871 with
                                  | (a,uu____69880) ->
                                      let uu____69885 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____69885 with
                                       | (field_name,uu____69891) ->
                                           let field_proj_tm =
                                             let uu____69893 =
                                               let uu____69894 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____69894
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____69893 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____69920 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____69962  ->
                                    match uu____69962 with
                                    | (x,uu____69973) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____69979 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____69979 with
                                         | (field_name,uu____69987) ->
                                             let t =
                                               let uu____69991 =
                                                 let uu____69992 =
                                                   let uu____69995 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____69995
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____69992
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____69991
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____70001 =
                                                    let uu____70003 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____70003.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____70001)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____70022 =
                                                   FStar_List.filter
                                                     (fun uu___590_70026  ->
                                                        match uu___590_70026
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____70029 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____70022
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_70044  ->
                                                         match uu___591_70044
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____70050 ->
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
                                               let uu____70061 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____70061;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____70063 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____70063
                                               then
                                                 let uu____70067 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____70067
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
                                                           fun uu____70121 
                                                             ->
                                                             match uu____70121
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
                                                                   let uu____70147
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____70147,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____70163
                                                                    =
                                                                    let uu____70166
                                                                    =
                                                                    let uu____70167
                                                                    =
                                                                    let uu____70174
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____70174,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____70167
                                                                     in
                                                                    pos
                                                                    uu____70166
                                                                     in
                                                                    (uu____70163,
                                                                    b))
                                                                   else
                                                                    (let uu____70182
                                                                    =
                                                                    let uu____70185
                                                                    =
                                                                    let uu____70186
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____70186
                                                                     in
                                                                    pos
                                                                    uu____70185
                                                                     in
                                                                    (uu____70182,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____70205 =
                                                     let uu____70208 =
                                                       let uu____70209 =
                                                         let uu____70223 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____70223,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____70209
                                                        in
                                                     pos uu____70208  in
                                                   let uu____70233 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____70205,
                                                     FStar_Pervasives_Native.None,
                                                     uu____70233)
                                                    in
                                                 let body =
                                                   let uu____70249 =
                                                     let uu____70256 =
                                                       let uu____70257 =
                                                         let uu____70280 =
                                                           let uu____70297 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____70297]  in
                                                         (arg_exp,
                                                           uu____70280)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____70257
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____70256
                                                      in
                                                   uu____70249
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____70362 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____70362
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
                                                   let uu____70381 =
                                                     let uu____70386 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____70386
                                                      in
                                                   let uu____70387 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____70381;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____70387;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____70393 =
                                                     let uu____70394 =
                                                       let uu____70401 =
                                                         let uu____70404 =
                                                           let uu____70405 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____70405
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____70404]  in
                                                       ((false, [lb]),
                                                         uu____70401)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____70394
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____70393;
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
                                                 (let uu____70419 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____70419
                                                  then
                                                    let uu____70423 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____70423
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____69920 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____70477) when
              let uu____70484 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____70484 ->
              let uu____70486 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____70486 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____70508 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____70508 with
                    | (formals,uu____70526) ->
                        let uu____70547 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____70582 =
                                   let uu____70584 =
                                     let uu____70585 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____70585  in
                                   FStar_Ident.lid_equals typ_lid uu____70584
                                    in
                                 if uu____70582
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____70607,uvs',tps,typ0,uu____70611,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____70631 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____70680 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____70680
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____70547 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____70718 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____70718 with
                              | (indices,uu____70736) ->
                                  let refine_domain =
                                    let uu____70759 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_70766  ->
                                              match uu___592_70766 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____70768 -> true
                                              | uu____70778 -> false))
                                       in
                                    if uu____70759
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_70793 =
                                      match uu___593_70793 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____70796,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____70808 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____70809 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____70809 with
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
                                    let uu____70822 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____70822 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____70905  ->
                                               fun uu____70906  ->
                                                 match (uu____70905,
                                                         uu____70906)
                                                 with
                                                 | ((x,uu____70932),(x',uu____70934))
                                                     ->
                                                     let uu____70955 =
                                                       let uu____70962 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____70962)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____70955) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____70967 -> []
  