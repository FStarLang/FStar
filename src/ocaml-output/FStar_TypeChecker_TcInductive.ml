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
          let uu____496 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____496 with
           | (usubst,uvs1) ->
               let uu____592 =
                 let uu____657 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____766 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____767 =
                   let uu____776 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____776 k  in
                 (uu____657, uu____766, uu____767)  in
               (match uu____592 with
                | (env1,tps1,k1) ->
                    let uu____1038 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____1038 with
                     | (tps2,k2) ->
                         let uu____1128 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____1128 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____1386 =
                                let uu____1418 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____1418 with
                                | (k3,uu____1473,g) ->
                                    let k4 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Exclude
                                           FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Zeta;
                                        FStar_TypeChecker_Env.Eager_unfolding
                                          false;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3
                                       in
                                    let uu____1517 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____1541 =
                                      let uu____1550 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____1550
                                       in
                                    (uu____1517, uu____1541)
                                 in
                              (match uu____1386 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____1740 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____1740
                                      in
                                   let uu____1751 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____1751 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____1844 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____1844))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____1851 =
                                              let uu____1857 =
                                                let uu____1859 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____1861 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____1859 uu____1861
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____1857)
                                               in
                                            FStar_Errors.raise_error
                                              uu____1851
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
                                            let uu____1890 =
                                              let uu____1904 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____1931 =
                                                let uu____1945 =
                                                  let uu____1963 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____1963
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____1945
                                                 in
                                              FStar_List.append uu____1904
                                                uu____1931
                                               in
                                            let uu____2001 =
                                              let uu____2012 =
                                                let uu____2021 =
                                                  let uu____2034 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____2034
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____2021
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____2012
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____1890 uu____2001
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____2077 =
                                            let uu____2086 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____2087 =
                                              let uu____2096 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____2096 k4
                                               in
                                            (uu____2086, uu____2087)  in
                                          match uu____2077 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____2202 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____2202,
                                                (let uu___61_2393 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___61_2393.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___61_2393.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___61_2393.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___61_2393.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____2424 -> failwith "impossible"
  
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
            let uu____2743 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____2743 with
             | (usubst,_uvs1) ->
                 let uu____2781 =
                   let uu____2844 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____2953 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____2844, uu____2953)  in
                 (match uu____2781 with
                  | (env1,t1) ->
                      let uu____3151 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____3357  ->
                               match uu____3357 with
                               | (se1,u_tc) ->
                                   let uu____3441 =
                                     let uu____3443 =
                                       let uu____3452 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____3452  in
                                     FStar_Ident.lid_equals tc_lid uu____3443
                                      in
                                   if uu____3441
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____3588,uu____3589,tps,uu____3591,uu____3592,uu____3593)
                                          ->
                                          let tps1 =
                                            let uu____3635 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____3635
                                              (FStar_List.map
                                                 (fun uu____3700  ->
                                                    match uu____3700 with
                                                    | (x,uu____3724) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____3747 =
                                            let uu____3808 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____3808, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____3747
                                      | uu____4031 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____4398 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____4398
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____3151 with
                       | (env2,tps,u_tc) ->
                           let uu____4714 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____4747 =
                               let uu____4748 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____4748.FStar_Syntax_Syntax.n  in
                             match uu____4747 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____4822 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____4822 with
                                  | (uu____4887,bs') ->
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
                                                fun uu____5005  ->
                                                  match uu____5005 with
                                                  | (x,uu____5019) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____5041 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____5041)
                             | uu____5050 -> ([], t2)  in
                           (match uu____4714 with
                            | (arguments,result) ->
                                ((let uu____5135 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____5135
                                  then
                                    let uu____5138 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____5140 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____5143 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____5138 uu____5140 uu____5143
                                  else ());
                                 (let uu____5148 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____5148 with
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
                                      let uu____5453 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____5453 with
                                       | (result1,res_lcomp) ->
                                           let uu____5509 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____5509 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____5604 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____5604
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____5720  ->
                                                      fun uu____5721  ->
                                                        match (uu____5720,
                                                                uu____5721)
                                                        with
                                                        | ((bv,uu____5769),
                                                           (t2,uu____5771))
                                                            ->
                                                            let uu____5825 =
                                                              let uu____5826
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____5826.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____5825
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____5843 ->
                                                                 let uu____5844
                                                                   =
                                                                   let uu____5850
                                                                    =
                                                                    let uu____5852
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____5854
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____5852
                                                                    uu____5854
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____5850)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____5844
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____5867 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____5867
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____5885 =
                                                     let uu____5886 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____5886.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____5885 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____5897 -> ()
                                                   | uu____5898 ->
                                                       let uu____5899 =
                                                         let uu____5905 =
                                                           let uu____5907 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____5909 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____5907
                                                             uu____5909
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____5905)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____5899
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____5922 =
                                                       let uu____5923 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____5923.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____5922 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5939;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5940;_},tuvs)
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
                                                                    let uu____5983
                                                                    =
                                                                    let uu____5992
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____6001
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
                                                                    uu____5992
                                                                    uu____6001
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5983)
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
                                                     | uu____6022 ->
                                                         let uu____6023 =
                                                           let uu____6029 =
                                                             let uu____6031 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____6033 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____6031
                                                               uu____6033
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____6029)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____6023
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____6072  ->
                                                            fun u_x  ->
                                                              match uu____6072
                                                              with
                                                              | (x,uu____6094)
                                                                  ->
                                                                  let uu____6109
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____6109)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____6129 =
                                                       let uu____6143 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____6208
                                                                  ->
                                                                 match uu____6208
                                                                 with
                                                                 | (x,uu____6232)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____6143
                                                         arguments1
                                                        in
                                                     let uu____6266 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____6129 uu____6266
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___183_6296 = se
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
                                                         (uu___183_6296.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___183_6296.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___183_6296.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___183_6296.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____6330 -> failwith "impossible"
  
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
            let uu___191_6580 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___191_6580.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___191_6580.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___191_6580.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____6598 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____6598
           then
             let uu____6603 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____6603
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____6666  ->
                     match uu____6666 with
                     | (se,uu____6677) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____6688,uu____6689,tps,k,uu____6692,uu____6693)
                              ->
                              let uu____6734 =
                                let uu____6743 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____6743
                                 in
                              FStar_Syntax_Syntax.null_binder uu____6734
                          | uu____6764 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____6818,uu____6819,t,uu____6821,uu____6822,uu____6823)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____6862 -> failwith "Impossible"))
              in
           let t =
             let uu____6875 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____6875
              in
           (let uu____6898 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____6898
            then
              let uu____6903 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____6903
            else ());
           (let uu____6908 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____6908 with
            | (uvs,t1) ->
                ((let uu____6950 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____6950
                  then
                    let uu____6955 =
                      let uu____6957 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____6957
                        (FStar_String.concat ", ")
                       in
                    let uu____6980 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____6955 uu____6980
                  else ());
                 (let uu____6985 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____6985 with
                  | (uvs1,t2) ->
                      let uu____7022 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____7022 with
                       | (args,uu____7065) ->
                           let uu____7104 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____7104 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____7279  ->
                                       fun uu____7280  ->
                                         match (uu____7279, uu____7280) with
                                         | ((x,uu____7327),(se,uu____7329))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____7380,tps,uu____7382,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____7434 =
                                                    let uu____7443 =
                                                      let uu____7444 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____7444.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____7443 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____7503 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____7503
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____7642
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____7679 -> ([], ty)
                                                     in
                                                  (match uu____7434 with
                                                   | (tps1,t3) ->
                                                       let uu___268_7710 = se
                                                          in
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
                                                           (uu___268_7710.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___268_7710.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___268_7710.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___268_7710.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____7741 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____7765 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _7773  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _7773))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___0_7806  ->
                                                match uu___0_7806 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____7821,uu____7822,uu____7823,uu____7824,uu____7825);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____7826;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____7827;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____7828;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____7829;_}
                                                    -> (tc, uvs_universes)
                                                | uu____7884 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____7932  ->
                                           fun d  ->
                                             match uu____7932 with
                                             | (t3,uu____7956) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____7977,uu____7978,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____8029 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8029
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___304_8046 = d
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
                                                          (uu___304_8046.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___304_8046.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___304_8046.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___304_8046.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____8076 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____8218 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____8218
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____8256 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____8256
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____8295 =
      let uu____8296 = FStar_Syntax_Subst.compress t  in
      uu____8296.FStar_Syntax_Syntax.n  in
    match uu____8295 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____8349 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____8358 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____8518 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____8583  ->
               match uu____8583 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____8655 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____8655  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____8518
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____9222 =
             let uu____9224 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____9224
              in
           debug_log env uu____9222);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype
              in
           (let uu____9237 =
              let uu____9239 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____9239
               in
            debug_log env uu____9237);
           (let uu____9244 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____9244) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____9257 =
                  let uu____9258 = FStar_Syntax_Subst.compress btype1  in
                  uu____9258.FStar_Syntax_Syntax.n  in
                match uu____9257 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____9312 = try_get_fv t  in
                    (match uu____9312 with
                     | (fv,us) ->
                         let uu____9329 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____9329
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____9353  ->
                                 match uu____9353 with
                                 | (t1,uu____9366) ->
                                     let uu____9379 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____9379) args)
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
                          let uu____9444 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____9444
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____9467 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____9467
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
                            (fun uu____9499  ->
                               match uu____9499 with
                               | (b,uu____9513) ->
                                   let uu____9528 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____9528) sbs)
                           &&
                           ((let uu____9534 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____9534 with
                             | (uu____9544,return_type) ->
                                 let uu____9554 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____9554)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____9663 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____9670 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____9675) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____9691) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____9716,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____9813  ->
                          match uu____9813 with
                          | (p,uu____9834,t) ->
                              let bs =
                                let uu____9874 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____9874
                                 in
                              let uu____9898 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____9898 with
                               | (bs1,t1) ->
                                   let uu____9918 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____9918)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____10028,uu____10029)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____10112 ->
                    ((let uu____10114 =
                        let uu____10116 =
                          let uu____10118 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____10120 =
                            let uu____10122 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____10122  in
                          Prims.op_Hat uu____10118 uu____10120  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____10116
                         in
                      debug_log env uu____10114);
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
              (let uu____10197 =
                 let uu____10199 =
                   let uu____10201 =
                     let uu____10203 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____10203  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____10201  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____10199
                  in
               debug_log env uu____10197);
              (let uu____10207 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____10207 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____10238 =
                       let uu____10240 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____10240
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____10238
                      then
                        ((let uu____10250 =
                            let uu____10252 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____10252
                             in
                          debug_log env uu____10250);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____10263 =
                        already_unfolded ilid args unfolded env  in
                      if uu____10263
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____10274 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____10274  in
                         (let uu____10280 =
                            let uu____10282 =
                              let uu____10284 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____10284
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____10282
                             in
                          debug_log env uu____10280);
                         (let uu____10289 =
                            let uu____10290 = FStar_ST.op_Bang unfolded  in
                            let uu____10320 =
                              let uu____10331 =
                                let uu____10340 =
                                  let uu____10341 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____10341  in
                                (ilid, uu____10340)  in
                              [uu____10331]  in
                            FStar_List.append uu____10290 uu____10320  in
                          FStar_ST.op_Colon_Equals unfolded uu____10289);
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
                  (let uu____10550 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____10550 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____10587 ->
                                   failwith
                                     "Impossible! Expected universe unification variables")
                          univ_unif_vars us;
                        (let dt1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant;
                             FStar_TypeChecker_Env.Iota;
                             FStar_TypeChecker_Env.Zeta;
                             FStar_TypeChecker_Env.AllowUnboundUniverses] env
                             dt
                            in
                         (let uu____10599 =
                            let uu____10601 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____10601
                             in
                          debug_log env uu____10599);
                         (let uu____10604 =
                            let uu____10605 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____10605.FStar_Syntax_Syntax.n  in
                          match uu____10604 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____10659 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____10659 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____10758 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____10758 dbs1
                                       in
                                    let c1 =
                                      let uu____10770 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____10770 c
                                       in
                                    let uu____10773 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____10773 with
                                     | (args1,uu____10820) ->
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
                                           let uu____10972 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____10972 c1
                                            in
                                         ((let uu____10987 =
                                             let uu____10989 =
                                               let uu____10991 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____10994 =
                                                 let uu____10996 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____10996
                                                  in
                                               Prims.op_Hat uu____10991
                                                 uu____10994
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____10989
                                              in
                                           debug_log env uu____10987);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____11019 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____11022 =
                                  let uu____11023 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____11023.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____11022
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
                   (let uu____11148 = try_get_fv t1  in
                    match uu____11148 with
                    | (fv,uu____11158) ->
                        let uu____11165 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____11165
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____11219 =
                      let uu____11221 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____11221
                       in
                    debug_log env uu____11219);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____11226 =
                      FStar_List.fold_left
                        (fun uu____11360  ->
                           fun b  ->
                             match uu____11360 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____11720 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____11729 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____11720, uu____11729))) (true, env)
                        sbs1
                       in
                    match uu____11226 with | (b,uu____11973) -> b))
              | uu____12084 ->
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
              let uu____12244 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____12244 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____12281 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____12284 =
                      let uu____12286 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____12286
                       in
                    debug_log env uu____12284);
                   (let uu____12289 =
                      let uu____12290 = FStar_Syntax_Subst.compress dt  in
                      uu____12290.FStar_Syntax_Syntax.n  in
                    match uu____12289 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____12302 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____12310) ->
                        let dbs1 =
                          let uu____12363 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____12363  in
                        let dbs2 =
                          let uu____12443 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____12443 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____12448 =
                            let uu____12450 =
                              let uu____12452 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____12452 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____12450
                             in
                          debug_log env uu____12448);
                         (let uu____12467 =
                            FStar_List.fold_left
                              (fun uu____12601  ->
                                 fun b  ->
                                   match uu____12601 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____12961 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____12970 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____12961, uu____12970)))
                              (true, env) dbs3
                             in
                          match uu____12467 with | (b,uu____13214) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____13325,uu____13326) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____13386 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____13531 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____13555,uu____13556,uu____13557) -> (lid, us, bs)
        | uu____13602 -> failwith "Impossible!"  in
      match uu____13531 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____13626 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____13626 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____13872 =
                 let uu____13879 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____13879  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____13909 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____13909
                      unfolded_inductives env2) uu____13872)
  
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
        (uu____14091,uu____14092,t,uu____14094,uu____14095,uu____14096) -> t
    | uu____14135 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____14164 =
         let uu____14166 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____14166 haseq_suffix  in
       uu____14164 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____14188 =
      let uu____14193 =
        let uu____14198 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____14198]  in
      FStar_List.append lid.FStar_Ident.ns uu____14193  in
    FStar_Ident.lid_of_ids uu____14188
  
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
          let uu____14396 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____14426,bs,t,uu____14429,uu____14430) ->
                (lid, bs, t)
            | uu____14479 -> failwith "Impossible!"  in
          match uu____14396 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____14546 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____14546 t  in
              let uu____14560 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____14560 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____14602 =
                       let uu____14603 = FStar_Syntax_Subst.compress t2  in
                       uu____14603.FStar_Syntax_Syntax.n  in
                     match uu____14602 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____14615) -> ibs
                     | uu____14654 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____14676 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____14685 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____14676 uu____14685
                      in
                   let ind1 =
                     let uu____14703 =
                       let uu____14708 =
                         FStar_List.map
                           (fun uu____14734  ->
                              match uu____14734 with
                              | (bv,aq) ->
                                  let uu____14772 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____14772, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____14708  in
                     uu____14703 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____14798 =
                       let uu____14803 =
                         FStar_List.map
                           (fun uu____14829  ->
                              match uu____14829 with
                              | (bv,aq) ->
                                  let uu____14867 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____14867, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____14803  in
                     uu____14798 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____14893 =
                       let uu____14898 =
                         let uu____14899 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____14899]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____14898
                        in
                     uu____14893 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____14975 =
                            let uu____14984 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____14984  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____14975) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____15026 =
                              let uu____15037 =
                                let uu____15042 =
                                  let uu____15043 =
                                    let uu____15056 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____15056
                                     in
                                  [uu____15043]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____15042
                                 in
                              uu____15037 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____15026)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___638_15116 = fml  in
                     let uu____15125 =
                       let uu____15126 =
                         let uu____15137 =
                           let uu____15138 =
                             let uu____15167 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____15176 =
                               let uu____15193 =
                                 let uu____15208 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____15208]  in
                               [uu____15193]  in
                             (uu____15167, uu____15176)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____15138  in
                         (fml, uu____15137)  in
                       FStar_Syntax_Syntax.Tm_meta uu____15126  in
                     {
                       FStar_Syntax_Syntax.n = uu____15125;
                       FStar_Syntax_Syntax.pos =
                         (uu___638_15116.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___638_15116.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____15325 =
                              let uu____15330 =
                                let uu____15331 =
                                  let uu____15344 =
                                    let uu____15353 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____15353
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____15344  in
                                [uu____15331]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____15330
                               in
                            uu____15325 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____15475 =
                              let uu____15480 =
                                let uu____15481 =
                                  let uu____15494 =
                                    let uu____15503 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____15503
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____15494  in
                                [uu____15481]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____15480
                               in
                            uu____15475 FStar_Pervasives_Native.None
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
          let uu____15693 =
            let uu____15694 = FStar_Syntax_Subst.compress dt1  in
            uu____15694.FStar_Syntax_Syntax.n  in
          match uu____15693 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____15710) ->
              let dbs1 =
                let uu____15763 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____15763  in
              let dbs2 =
                let uu____15843 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____15843 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____15882 =
                           let uu____15887 =
                             let uu____15888 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____15888]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____15887
                            in
                         uu____15882 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____15949 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____15949 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____15965 =
                       let uu____15970 =
                         let uu____15971 =
                           let uu____15984 =
                             let uu____15993 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____15993
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____15984  in
                         [uu____15971]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____15970
                        in
                     uu____15965 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____16093 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____16420,uu____16421,uu____16422,uu____16423,uu____16424)
                  -> lid
              | uu____16465 -> failwith "Impossible!"  in
            let uu____16471 = acc  in
            match uu____16471 with
            | (uu____16648,en,uu____16650,uu____16651) ->
                let uu____16812 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____16812 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____16963 = acc  in
                     (match uu____16963 with
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
                                     (uu____17549,uu____17550,uu____17551,t_lid,uu____17553,uu____17554)
                                     -> t_lid = lid
                                 | uu____17597 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____17638 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____17638)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____17649 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____17660 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____17649, uu____17660)))
  
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
          let uu____17976 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18009,us,uu____18011,t,uu____18013,uu____18014) ->
                (us, t)
            | uu____18059 -> failwith "Impossible!"  in
          match uu____17976 with
          | (us,t) ->
              let uu____18086 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____18086 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____18339 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____18339 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____18793 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____18793 with
                           | (uu____18821,t1) ->
                               let uu____18861 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____18861
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____18870 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____18870 with
                          | (phi1,uu____18895) ->
                              ((let uu____18921 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____18921
                                then
                                  let uu____18924 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____18924
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____18968  ->
                                         match uu____18968 with
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
                let uu____19164 =
                  let uu____19165 = FStar_Syntax_Subst.compress t  in
                  uu____19165.FStar_Syntax_Syntax.n  in
                match uu____19164 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____19196) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____19275 = is_mutual t'  in
                    if uu____19275
                    then true
                    else
                      (let uu____19282 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____19282)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____19318) ->
                    is_mutual t'
                | uu____19331 -> false
              
              and exists_mutual uu___1_19333 =
                match uu___1_19333 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____19390 =
                let uu____19391 = FStar_Syntax_Subst.compress dt1  in
                uu____19391.FStar_Syntax_Syntax.n  in
              match uu____19390 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____19409) ->
                  let dbs1 =
                    let uu____19462 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____19462  in
                  let dbs2 =
                    let uu____19542 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____19542 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____19599 =
                               let uu____19604 =
                                 let uu____19605 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____19605]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____19604
                                in
                             uu____19599 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____19660 = is_mutual sort  in
                             if uu____19660
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
                           let uu____19693 =
                             let uu____19698 =
                               let uu____19699 =
                                 let uu____19712 =
                                   let uu____19721 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____19721 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____19712  in
                               [uu____19699]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____19698
                              in
                           uu____19693 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____19821 -> acc
  
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
              let uu____19915 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____19961,bs,t,uu____19964,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____20020 -> failwith "Impossible!"  in
              match uu____19915 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____20092 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____20092 t  in
                  let uu____20106 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____20106 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____20132 =
                           let uu____20133 = FStar_Syntax_Subst.compress t2
                              in
                           uu____20133.FStar_Syntax_Syntax.n  in
                         match uu____20132 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____20145) ->
                             ibs
                         | uu____20184 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____20206 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____20215 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____20206
                           uu____20215
                          in
                       let ind1 =
                         let uu____20233 =
                           let uu____20238 =
                             FStar_List.map
                               (fun uu____20264  ->
                                  match uu____20264 with
                                  | (bv,aq) ->
                                      let uu____20302 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____20302, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____20238  in
                         uu____20233 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____20328 =
                           let uu____20333 =
                             FStar_List.map
                               (fun uu____20359  ->
                                  match uu____20359 with
                                  | (bv,aq) ->
                                      let uu____20397 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____20397, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____20333  in
                         uu____20328 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____20423 =
                           let uu____20428 =
                             let uu____20429 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____20429]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____20428
                            in
                         uu____20423 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____20493,uu____20494,uu____20495,t_lid,uu____20497,uu____20498)
                                  -> t_lid = lid
                              | uu____20541 -> failwith "Impossible")
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
                         let uu___875_20586 = fml  in
                         let uu____20595 =
                           let uu____20596 =
                             let uu____20607 =
                               let uu____20608 =
                                 let uu____20637 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____20646 =
                                   let uu____20663 =
                                     let uu____20678 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____20678]  in
                                   [uu____20663]  in
                                 (uu____20637, uu____20646)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____20608
                                in
                             (fml, uu____20607)  in
                           FStar_Syntax_Syntax.Tm_meta uu____20596  in
                         {
                           FStar_Syntax_Syntax.n = uu____20595;
                           FStar_Syntax_Syntax.pos =
                             (uu___875_20586.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___875_20586.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____20795 =
                                  let uu____20800 =
                                    let uu____20801 =
                                      let uu____20814 =
                                        let uu____20823 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____20823
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____20814
                                       in
                                    [uu____20801]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____20800
                                   in
                                uu____20795 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____20945 =
                                  let uu____20950 =
                                    let uu____20951 =
                                      let uu____20964 =
                                        let uu____20973 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____20973
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____20964
                                       in
                                    [uu____20951]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____20950
                                   in
                                uu____20945 FStar_Pervasives_Native.None
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
                     (lid,uu____21288,uu____21289,uu____21290,uu____21291,uu____21292)
                     -> lid
                 | uu____21333 -> failwith "Impossible!") tcs
             in
          let uu____21339 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____21374,uu____21375,uu____21376,uu____21377) ->
                (lid, us)
            | uu____21422 -> failwith "Impossible!"  in
          match uu____21339 with
          | (lid,us) ->
              let uu____21449 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____21449 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____21514 =
                       let uu____21515 =
                         let uu____21530 = get_haseq_axiom_lid lid  in
                         (uu____21530, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____21515  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____21514;
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
          let uu____21770 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_21825  ->
                    match uu___2_21825 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____21832;
                        FStar_Syntax_Syntax.sigrng = uu____21833;
                        FStar_Syntax_Syntax.sigquals = uu____21834;
                        FStar_Syntax_Syntax.sigmeta = uu____21835;
                        FStar_Syntax_Syntax.sigattrs = uu____21836;_} -> true
                    | uu____21880 -> false))
             in
          match uu____21770 with
          | (tys,datas) ->
              ((let uu____21943 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_21964  ->
                          match uu___3_21964 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____21971;
                              FStar_Syntax_Syntax.sigrng = uu____21972;
                              FStar_Syntax_Syntax.sigquals = uu____21973;
                              FStar_Syntax_Syntax.sigmeta = uu____21974;
                              FStar_Syntax_Syntax.sigattrs = uu____21975;_}
                              -> false
                          | uu____22018 -> true))
                   in
                if uu____21943
                then
                  let uu____22026 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____22026
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____22052 =
                       let uu____22053 = FStar_List.hd tys  in
                       uu____22053.FStar_Syntax_Syntax.sigel  in
                     match uu____22052 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____22073,uvs,uu____22075,uu____22076,uu____22077,uu____22078)
                         -> uvs
                     | uu____22119 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____22234 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____22458 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____22458 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____22586,bs,t,l1,l2) ->
                                      let uu____22631 =
                                        let uu____22664 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____22665 =
                                          let uu____22674 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____22674 t
                                           in
                                        (lid, univs2, uu____22664,
                                          uu____22665, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____22631
                                  | uu____22708 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___971_22710 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___971_22710.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___971_22710.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___971_22710.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___971_22710.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____22750,t,lid_t,x,l) ->
                                      let uu____22793 =
                                        let uu____22825 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____22825, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____22793
                                  | uu____22853 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___985_22855 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___985_22855.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___985_22855.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___985_22855.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___985_22855.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____22866 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____22866, tys1, datas1))
                   in
                match uu____22234 with
                | (env1,tys1,datas1) ->
                    let uu____23207 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____23377  ->
                             match uu____23377 with
                             | (env2,all_tcs,g) ->
                                 let uu____23674 = tc_tycon env2 tc  in
                                 (match uu____23674 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____23961 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____23961
                                        then
                                          let uu____23964 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____23964
                                        else ());
                                       (let uu____23969 =
                                          let uu____23978 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____23978
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____23969))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____23207 with
                     | (env2,tcs,g) ->
                         let uu____24314 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____24359  ->
                                  match uu____24359 with
                                  | (datas2,g1) ->
                                      let uu____24419 =
                                        let uu____24433 = tc_data env2 tcs
                                           in
                                        uu____24433 se  in
                                      (match uu____24419 with
                                       | (data,g') ->
                                           let uu____24491 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____24491)))
                             datas1 ([], g)
                            in
                         (match uu____24314 with
                          | (datas2,g1) ->
                              let uu____24581 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____24625 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____24625, datas2))
                                 in
                              (match uu____24581 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____24732 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____24733 =
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
                                         uu____24732;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____24733
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____24806,uu____24807)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____24859 =
                                                    let uu____24865 =
                                                      let uu____24867 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____24869 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____24867
                                                        uu____24869
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____24865)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____24859
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____24873 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____24873 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____24889)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____24943 ->
                                                             let uu____24944
                                                               =
                                                               let uu____24951
                                                                 =
                                                                 let uu____24952
                                                                   =
                                                                   let uu____24976
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____24976)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____24952
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____24951
                                                                in
                                                             uu____24944
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
                                                       let uu____25031 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____25031
                                                        with
                                                        | (uu____25040,inferred)
                                                            ->
                                                            let uu____25050 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____25050
                                                             with
                                                             | (uu____25059,expected)
                                                                 ->
                                                                 let uu____25069
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____25069
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____25076 -> ()));
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
                          let uu____25372 =
                            let uu____25379 =
                              let uu____25380 =
                                let uu____25391 =
                                  let uu____25402 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____25402
                                   in
                                (uu____25391, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____25380  in
                            FStar_Syntax_Syntax.mk uu____25379  in
                          uu____25372 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____25465  ->
                                  match uu____25465 with
                                  | (x,imp) ->
                                      let uu____25503 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____25503, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____25519 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____25519  in
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
                               let uu____25596 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____25596
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____25606 =
                               let uu____25617 =
                                 let uu____25628 =
                                   let uu____25633 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____25642 =
                                     let uu____25643 =
                                       let uu____25656 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____25656
                                        in
                                     [uu____25643]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____25633
                                     uu____25642
                                    in
                                 uu____25628 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____25617  in
                             FStar_Syntax_Util.refine x uu____25606  in
                           let uu____25705 =
                             let uu___1086_25716 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1086_25716.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1086_25716.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____25705)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____25753 =
                          FStar_List.map
                            (fun uu____25792  ->
                               match uu____25792 with
                               | (x,uu____25816) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____25753 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____25925  ->
                                match uu____25925 with
                                | (x,uu____25949) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____25975 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____25975)
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
                               (let uu____26027 =
                                  let uu____26029 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____26029.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____26027)
                              in
                           let quals =
                             let uu____26041 =
                               FStar_List.filter
                                 (fun uu___4_26045  ->
                                    match uu___4_26045 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____26050 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____26041
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____26124 =
                                 let uu____26133 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____26133  in
                               FStar_Syntax_Syntax.mk_Total uu____26124  in
                             let uu____26140 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____26140
                              in
                           let decl =
                             let uu____26170 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____26170;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____26184 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____26184
                            then
                              let uu____26188 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____26188
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
                                             fun uu____26295  ->
                                               match uu____26295 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____26341 =
                                                       let uu____26347 =
                                                         let uu____26348 =
                                                           let uu____26364 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____26364,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____26348
                                                          in
                                                       pos uu____26347  in
                                                     (uu____26341, b)
                                                   else
                                                     (let uu____26394 =
                                                        let uu____26400 =
                                                          let uu____26401 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____26401
                                                           in
                                                        pos uu____26400  in
                                                      (uu____26394, b))))
                                      in
                                   let pat_true =
                                     let uu____26444 =
                                       let uu____26450 =
                                         let uu____26451 =
                                           let uu____26471 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____26471, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____26451
                                          in
                                       pos uu____26450  in
                                     (uu____26444,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____26544 =
                                       let uu____26550 =
                                         let uu____26551 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____26551
                                          in
                                       pos uu____26550  in
                                     (uu____26544,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____26603 =
                                     let uu____26610 =
                                       let uu____26611 =
                                         let uu____26649 =
                                           let uu____26677 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____26703 =
                                             let uu____26731 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____26731]  in
                                           uu____26677 :: uu____26703  in
                                         (arg_exp, uu____26649)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____26611
                                        in
                                     FStar_Syntax_Syntax.mk uu____26610  in
                                   uu____26603 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____26866 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____26866
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
                                let uu____26929 =
                                  let uu____26942 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____26942  in
                                let uu____26957 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____26929
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____26957 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____26985 =
                                  let uu____26986 =
                                    let uu____26997 =
                                      let uu____27004 =
                                        let uu____27013 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____27013
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____27004]  in
                                    ((false, [lb]), uu____26997)  in
                                  FStar_Syntax_Syntax.Sig_let uu____26986  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____26985;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____27103 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____27103
                               then
                                 let uu____27107 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____27107
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
                                fun uu____27242  ->
                                  match uu____27242 with
                                  | (a,uu____27256) ->
                                      let uu____27271 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____27271 with
                                       | (field_name,uu____27286) ->
                                           let field_proj_tm =
                                             let uu____27314 =
                                               let uu____27323 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____27323
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____27314 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____27385 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____27452  ->
                                    match uu____27452 with
                                    | (x,uu____27473) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____27489 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____27489 with
                                         | (field_name,uu____27511) ->
                                             let t =
                                               let uu____27541 =
                                                 let uu____27550 =
                                                   let uu____27561 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____27561
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____27550
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____27541
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____27583 =
                                                    let uu____27585 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____27585.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____27583)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____27612 =
                                                   FStar_List.filter
                                                     (fun uu___5_27616  ->
                                                        match uu___5_27616
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____27619 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____27612
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___6_27634  ->
                                                         match uu___6_27634
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____27640 ->
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
                                               let uu____27687 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____27687;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____27697 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____27697
                                               then
                                                 let uu____27701 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____27701
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
                                                           fun uu____27799 
                                                             ->
                                                             match uu____27799
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
                                                                   let uu____27846
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____27846,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____27871
                                                                    =
                                                                    let uu____27877
                                                                    =
                                                                    let uu____27878
                                                                    =
                                                                    let uu____27894
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____27894,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____27878
                                                                     in
                                                                    pos
                                                                    uu____27877
                                                                     in
                                                                    (uu____27871,
                                                                    b))
                                                                   else
                                                                    (let uu____27924
                                                                    =
                                                                    let uu____27930
                                                                    =
                                                                    let uu____27931
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____27931
                                                                     in
                                                                    pos
                                                                    uu____27930
                                                                     in
                                                                    (uu____27924,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____27974 =
                                                     let uu____27980 =
                                                       let uu____27981 =
                                                         let uu____28001 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____28001,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____27981
                                                        in
                                                     pos uu____27980  in
                                                   let uu____28023 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____27974,
                                                     FStar_Pervasives_Native.None,
                                                     uu____28023)
                                                    in
                                                 let body =
                                                   let uu____28070 =
                                                     let uu____28077 =
                                                       let uu____28078 =
                                                         let uu____28116 =
                                                           let uu____28144 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____28144]  in
                                                         (arg_exp,
                                                           uu____28116)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____28078
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____28077
                                                      in
                                                   uu____28070
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____28272 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____28272
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
                                                   let uu____28317 =
                                                     let uu____28330 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____28330
                                                      in
                                                   let uu____28345 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____28317;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____28345;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____28373 =
                                                     let uu____28374 =
                                                       let uu____28385 =
                                                         let uu____28392 =
                                                           let uu____28401 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____28401
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____28392]  in
                                                       ((false, [lb]),
                                                         uu____28385)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____28374
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____28373;
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
                                                 (let uu____28487 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____28487
                                                  then
                                                    let uu____28491 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____28491
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____27385 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____28733) when
              let uu____28772 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____28772 ->
              let uu____28774 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____28774 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____28815 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____28815 with
                    | (formals,uu____28847) ->
                        let uu____28886 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____28943 =
                                   let uu____28945 =
                                     let uu____28954 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____28954  in
                                   FStar_Ident.lid_equals typ_lid uu____28945
                                    in
                                 if uu____28943
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____28992,uvs',tps,typ0,uu____28996,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____29060 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____29133 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____29133
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____28886 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____29209 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____29209 with
                              | (indices,uu____29241) ->
                                  let refine_domain =
                                    let uu____29282 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_29289  ->
                                              match uu___7_29289 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____29291 -> true
                                              | uu____29305 -> false))
                                       in
                                    if uu____29282
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_29320 =
                                      match uu___8_29320 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____29323,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____29349 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____29350 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____29350 with
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
                                    let uu____29363 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____29363 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____29491  ->
                                               fun uu____29492  ->
                                                 match (uu____29491,
                                                         uu____29492)
                                                 with
                                                 | ((x,uu____29538),(x',uu____29540))
                                                     ->
                                                     let uu____29591 =
                                                       let uu____29607 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____29607)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____29591) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____29629 -> []
  