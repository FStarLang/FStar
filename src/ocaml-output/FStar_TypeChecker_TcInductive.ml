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
          let uu____61432 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____61432 with
           | (usubst,uvs1) ->
               let uu____61459 =
                 let uu____61466 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____61467 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____61468 =
                   let uu____61469 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____61469 k  in
                 (uu____61466, uu____61467, uu____61468)  in
               (match uu____61459 with
                | (env1,tps1,k1) ->
                    let uu____61489 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____61489 with
                     | (tps2,k2) ->
                         let uu____61504 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____61504 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____61525 =
                                let uu____61544 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____61544 with
                                | (k3,uu____61570,g) ->
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
                                    let uu____61573 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____61588 =
                                      let uu____61589 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____61589
                                       in
                                    (uu____61573, uu____61588)
                                 in
                              (match uu____61525 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____61652 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____61652
                                      in
                                   let uu____61655 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____61655 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____61673 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____61673))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____61680 =
                                              let uu____61686 =
                                                let uu____61688 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____61690 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____61688 uu____61690
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____61686)
                                               in
                                            FStar_Errors.raise_error
                                              uu____61680
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
                                            let uu____61703 =
                                              let uu____61712 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____61729 =
                                                let uu____61738 =
                                                  let uu____61751 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____61751
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____61738
                                                 in
                                              FStar_List.append uu____61712
                                                uu____61729
                                               in
                                            let uu____61774 =
                                              let uu____61777 =
                                                let uu____61778 =
                                                  let uu____61783 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____61783
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____61778
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____61777
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____61703 uu____61774
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____61800 =
                                            let uu____61805 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____61806 =
                                              let uu____61807 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____61807 k4
                                               in
                                            (uu____61805, uu____61806)  in
                                          match uu____61800 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____61827 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____61827,
                                                (let uu___646_61833 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_61833.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_61833.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_61833.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_61833.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____61838 -> failwith "impossible"
  
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
            let uu____61902 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____61902 with
             | (usubst,_uvs1) ->
                 let uu____61925 =
                   let uu____61930 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____61931 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____61930, uu____61931)  in
                 (match uu____61925 with
                  | (env1,t1) ->
                      let uu____61938 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____61977  ->
                               match uu____61977 with
                               | (se1,u_tc) ->
                                   let uu____61992 =
                                     let uu____61994 =
                                       let uu____61995 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____61995  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____61994
                                      in
                                   if uu____61992
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____62015,uu____62016,tps,uu____62018,uu____62019,uu____62020)
                                          ->
                                          let tps1 =
                                            let uu____62030 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____62030
                                              (FStar_List.map
                                                 (fun uu____62070  ->
                                                    match uu____62070 with
                                                    | (x,uu____62084) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____62092 =
                                            let uu____62099 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____62099, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____62092
                                      | uu____62106 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____62149 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____62149
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____61938 with
                       | (env2,tps,u_tc) ->
                           let uu____62181 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____62197 =
                               let uu____62198 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____62198.FStar_Syntax_Syntax.n  in
                             match uu____62197 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____62237 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____62237 with
                                  | (uu____62278,bs') ->
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
                                                fun uu____62349  ->
                                                  match uu____62349 with
                                                  | (x,uu____62358) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____62365 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____62365)
                             | uu____62366 -> ([], t2)  in
                           (match uu____62181 with
                            | (arguments,result) ->
                                ((let uu____62410 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____62410
                                  then
                                    let uu____62413 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____62415 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____62418 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____62413 uu____62415 uu____62418
                                  else ());
                                 (let uu____62423 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____62423 with
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
                                      let uu____62441 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____62441 with
                                       | (result1,res_lcomp) ->
                                           let uu____62452 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____62452 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____62510 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____62510
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____62592  ->
                                                      fun uu____62593  ->
                                                        match (uu____62592,
                                                                uu____62593)
                                                        with
                                                        | ((bv,uu____62623),
                                                           (t2,uu____62625))
                                                            ->
                                                            let uu____62652 =
                                                              let uu____62653
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____62653.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____62652
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____62657 ->
                                                                 let uu____62658
                                                                   =
                                                                   let uu____62664
                                                                    =
                                                                    let uu____62666
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____62668
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____62666
                                                                    uu____62668
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____62664)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____62658
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____62673 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____62673
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____62675 =
                                                     let uu____62676 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____62676.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____62675 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____62679 -> ()
                                                   | uu____62680 ->
                                                       let uu____62681 =
                                                         let uu____62687 =
                                                           let uu____62689 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____62691 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____62689
                                                             uu____62691
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____62687)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____62681
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____62696 =
                                                       let uu____62697 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____62697.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____62696 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____62701;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____62702;_},tuvs)
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
                                                                    let uu____62716
                                                                    =
                                                                    let uu____62717
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____62718
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
                                                                    uu____62717
                                                                    uu____62718
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62716)
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
                                                     | uu____62724 ->
                                                         let uu____62725 =
                                                           let uu____62731 =
                                                             let uu____62733
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____62735
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____62733
                                                               uu____62735
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____62731)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____62725
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____62753  ->
                                                            fun u_x  ->
                                                              match uu____62753
                                                              with
                                                              | (x,uu____62762)
                                                                  ->
                                                                  let uu____62767
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62767)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____62771 =
                                                       let uu____62780 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____62820 
                                                                 ->
                                                                 match uu____62820
                                                                 with
                                                                 | (x,uu____62834)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____62780
                                                         arguments1
                                                        in
                                                     let uu____62848 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____62771
                                                       uu____62848
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_62853 = se
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
                                                         (uu___768_62853.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_62853.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_62853.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_62853.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____62857 -> failwith "impossible"
  
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
            let uu___776_62924 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_62924.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_62924.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_62924.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____62934 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____62934
           then
             let uu____62939 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____62939
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____62982  ->
                     match uu____62982 with
                     | (se,uu____62988) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____62989,uu____62990,tps,k,uu____62993,uu____62994)
                              ->
                              let uu____63003 =
                                let uu____63004 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____63004
                                 in
                              FStar_Syntax_Syntax.null_binder uu____63003
                          | uu____63009 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____63038,uu____63039,t,uu____63041,uu____63042,uu____63043)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____63050 -> failwith "Impossible"))
              in
           let t =
             let uu____63055 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____63055
              in
           (let uu____63065 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____63065
            then
              let uu____63070 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____63070
            else ());
           (let uu____63075 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____63075 with
            | (uvs,t1) ->
                ((let uu____63095 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____63095
                  then
                    let uu____63100 =
                      let uu____63102 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____63102
                        (FStar_String.concat ", ")
                       in
                    let uu____63119 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____63100 uu____63119
                  else ());
                 (let uu____63124 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____63124 with
                  | (uvs1,t2) ->
                      let uu____63139 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____63139 with
                       | (args,uu____63163) ->
                           let uu____63184 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____63184 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____63289  ->
                                       fun uu____63290  ->
                                         match (uu____63289, uu____63290)
                                         with
                                         | ((x,uu____63312),(se,uu____63314))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____63330,tps,uu____63332,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____63344 =
                                                    let uu____63349 =
                                                      let uu____63350 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____63350.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____63349 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____63379 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____63379
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____63457
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____63476 -> ([], ty)
                                                     in
                                                  (match uu____63344 with
                                                   | (tps1,t3) ->
                                                       let uu___853_63485 =
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
                                                           (uu___853_63485.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_63485.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_63485.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_63485.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____63490 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____63497 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _63501  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _63501))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_63520  ->
                                                match uu___585_63520 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____63526,uu____63527,uu____63528,uu____63529,uu____63530);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____63531;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____63532;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____63533;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____63534;_}
                                                    -> (tc, uvs_universes)
                                                | uu____63547 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____63571  ->
                                           fun d  ->
                                             match uu____63571 with
                                             | (t3,uu____63580) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____63586,uu____63587,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____63598 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____63598
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_63599 = d
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
                                                          (uu___889_63599.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_63599.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_63599.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_63599.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____63603 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____63622 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____63622
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____63644 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____63644
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____63661 =
      let uu____63662 = FStar_Syntax_Subst.compress t  in
      uu____63662.FStar_Syntax_Syntax.n  in
    match uu____63661 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____63681 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____63687 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____63724 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____63773  ->
               match uu____63773 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____63817 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____63817  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____63724
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____64022 =
             let uu____64024 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____64024
              in
           debug_log env uu____64022);
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
           (let uu____64029 =
              let uu____64031 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____64031
               in
            debug_log env uu____64029);
           (let uu____64036 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____64036) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____64049 =
                  let uu____64050 = FStar_Syntax_Subst.compress btype1  in
                  uu____64050.FStar_Syntax_Syntax.n  in
                match uu____64049 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____64080 = try_get_fv t  in
                    (match uu____64080 with
                     | (fv,us) ->
                         let uu____64088 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____64088
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____64104  ->
                                 match uu____64104 with
                                 | (t1,uu____64113) ->
                                     let uu____64118 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____64118) args)
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
                          let uu____64153 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____64153
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____64157 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____64157
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
                            (fun uu____64184  ->
                               match uu____64184 with
                               | (b,uu____64193) ->
                                   let uu____64198 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____64198) sbs)
                           &&
                           ((let uu____64204 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____64204 with
                             | (uu____64210,return_type) ->
                                 let uu____64212 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____64212)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____64213 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____64217 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____64222) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____64230) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____64237,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____64296  ->
                          match uu____64296 with
                          | (p,uu____64309,t) ->
                              let bs =
                                let uu____64328 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____64328
                                 in
                              let uu____64337 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____64337 with
                               | (bs1,t1) ->
                                   let uu____64345 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____64345)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____64347,uu____64348)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____64391 ->
                    ((let uu____64393 =
                        let uu____64395 =
                          let uu____64397 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____64399 =
                            let uu____64401 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____64401  in
                          Prims.op_Hat uu____64397 uu____64399  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____64395
                         in
                      debug_log env uu____64393);
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
              (let uu____64414 =
                 let uu____64416 =
                   let uu____64418 =
                     let uu____64420 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____64420  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____64418  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____64416
                  in
               debug_log env uu____64414);
              (let uu____64424 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____64424 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____64443 =
                       let uu____64445 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____64445
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____64443
                      then
                        ((let uu____64449 =
                            let uu____64451 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____64451
                             in
                          debug_log env uu____64449);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____64462 =
                        already_unfolded ilid args unfolded env  in
                      if uu____64462
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____64473 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____64473  in
                         (let uu____64479 =
                            let uu____64481 =
                              let uu____64483 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____64483
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____64481
                             in
                          debug_log env uu____64479);
                         (let uu____64488 =
                            let uu____64489 = FStar_ST.op_Bang unfolded  in
                            let uu____64515 =
                              let uu____64522 =
                                let uu____64527 =
                                  let uu____64528 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____64528  in
                                (ilid, uu____64527)  in
                              [uu____64522]  in
                            FStar_List.append uu____64489 uu____64515  in
                          FStar_ST.op_Colon_Equals unfolded uu____64488);
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
                  (let uu____64627 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____64627 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____64650 ->
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
                         (let uu____64654 =
                            let uu____64656 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____64656
                             in
                          debug_log env uu____64654);
                         (let uu____64659 =
                            let uu____64660 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____64660.FStar_Syntax_Syntax.n  in
                          match uu____64659 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____64688 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____64688 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____64752 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____64752 dbs1
                                       in
                                    let c1 =
                                      let uu____64756 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____64756 c
                                       in
                                    let uu____64759 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____64759 with
                                     | (args1,uu____64794) ->
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
                                           let uu____64886 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____64886 c1
                                            in
                                         ((let uu____64896 =
                                             let uu____64898 =
                                               let uu____64900 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____64903 =
                                                 let uu____64905 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____64905
                                                  in
                                               Prims.op_Hat uu____64900
                                                 uu____64903
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____64898
                                              in
                                           debug_log env uu____64896);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____64919 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____64922 =
                                  let uu____64923 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____64923.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____64922
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
                   (let uu____64962 = try_get_fv t1  in
                    match uu____64962 with
                    | (fv,uu____64969) ->
                        let uu____64970 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____64970
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____65002 =
                      let uu____65004 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____65004
                       in
                    debug_log env uu____65002);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____65009 =
                      FStar_List.fold_left
                        (fun uu____65030  ->
                           fun b  ->
                             match uu____65030 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____65061 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____65065 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____65061, uu____65065))) (true, env)
                        sbs1
                       in
                    match uu____65009 with | (b,uu____65083) -> b))
              | uu____65086 ->
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
              let uu____65122 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____65122 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____65145 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____65148 =
                      let uu____65150 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____65150
                       in
                    debug_log env uu____65148);
                   (let uu____65153 =
                      let uu____65154 = FStar_Syntax_Subst.compress dt  in
                      uu____65154.FStar_Syntax_Syntax.n  in
                    match uu____65153 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____65158 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____65163) ->
                        let dbs1 =
                          let uu____65193 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____65193  in
                        let dbs2 =
                          let uu____65243 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____65243 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____65248 =
                            let uu____65250 =
                              let uu____65252 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____65252 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____65250
                             in
                          debug_log env uu____65248);
                         (let uu____65262 =
                            FStar_List.fold_left
                              (fun uu____65283  ->
                                 fun b  ->
                                   match uu____65283 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____65314 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____65318 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____65314, uu____65318)))
                              (true, env) dbs3
                             in
                          match uu____65262 with | (b,uu____65336) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____65339,uu____65340) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____65376 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____65399 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____65415,uu____65416,uu____65417) -> (lid, us, bs)
        | uu____65426 -> failwith "Impossible!"  in
      match uu____65399 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____65438 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____65438 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____65462 =
                 let uu____65465 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____65465  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____65479 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____65479
                      unfolded_inductives env2) uu____65462)
  
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
        (uu____65514,uu____65515,t,uu____65517,uu____65518,uu____65519) -> t
    | uu____65526 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____65543 =
         let uu____65545 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____65545 haseq_suffix  in
       uu____65543 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____65555 =
      let uu____65558 =
        let uu____65561 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____65561]  in
      FStar_List.append lid.FStar_Ident.ns uu____65558  in
    FStar_Ident.lid_of_ids uu____65555
  
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
          let uu____65607 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____65621,bs,t,uu____65624,uu____65625) ->
                (lid, bs, t)
            | uu____65634 -> failwith "Impossible!"  in
          match uu____65607 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____65657 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____65657 t  in
              let uu____65666 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____65666 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____65684 =
                       let uu____65685 = FStar_Syntax_Subst.compress t2  in
                       uu____65685.FStar_Syntax_Syntax.n  in
                     match uu____65684 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____65689) -> ibs
                     | uu____65710 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____65719 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____65720 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____65719 uu____65720
                      in
                   let ind1 =
                     let uu____65726 =
                       let uu____65731 =
                         FStar_List.map
                           (fun uu____65748  ->
                              match uu____65748 with
                              | (bv,aq) ->
                                  let uu____65767 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65767, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____65731  in
                     uu____65726 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____65773 =
                       let uu____65778 =
                         FStar_List.map
                           (fun uu____65795  ->
                              match uu____65795 with
                              | (bv,aq) ->
                                  let uu____65814 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65814, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____65778  in
                     uu____65773 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____65820 =
                       let uu____65825 =
                         let uu____65826 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____65826]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____65825
                        in
                     uu____65820 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____65875 =
                            let uu____65876 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____65876  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____65875) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____65889 =
                              let uu____65892 =
                                let uu____65897 =
                                  let uu____65898 =
                                    let uu____65907 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____65907
                                     in
                                  [uu____65898]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____65897
                                 in
                              uu____65892 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____65889)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_65930 = fml  in
                     let uu____65931 =
                       let uu____65932 =
                         let uu____65939 =
                           let uu____65940 =
                             let uu____65953 =
                               let uu____65964 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____65964]  in
                             [uu____65953]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____65940  in
                         (fml, uu____65939)  in
                       FStar_Syntax_Syntax.Tm_meta uu____65932  in
                     {
                       FStar_Syntax_Syntax.n = uu____65931;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_65930.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_65930.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66017 =
                              let uu____66022 =
                                let uu____66023 =
                                  let uu____66032 =
                                    let uu____66033 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66033
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66032  in
                                [uu____66023]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66022
                               in
                            uu____66017 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66086 =
                              let uu____66091 =
                                let uu____66092 =
                                  let uu____66101 =
                                    let uu____66102 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66102
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66101  in
                                [uu____66092]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66091
                               in
                            uu____66086 FStar_Pervasives_Native.None
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
          let uu____66177 =
            let uu____66178 = FStar_Syntax_Subst.compress dt1  in
            uu____66178.FStar_Syntax_Syntax.n  in
          match uu____66177 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____66182) ->
              let dbs1 =
                let uu____66212 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____66212  in
              let dbs2 =
                let uu____66262 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____66262 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____66277 =
                           let uu____66282 =
                             let uu____66283 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____66283]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____66282
                            in
                         uu____66277 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____66314 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____66314 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____66322 =
                       let uu____66327 =
                         let uu____66328 =
                           let uu____66337 =
                             let uu____66338 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____66338
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____66337  in
                         [uu____66328]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____66327
                        in
                     uu____66322 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____66385 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____66476,uu____66477,uu____66478,uu____66479,uu____66480)
                  -> lid
              | uu____66489 -> failwith "Impossible!"  in
            let uu____66491 = acc  in
            match uu____66491 with
            | (uu____66528,en,uu____66530,uu____66531) ->
                let uu____66552 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____66552 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____66589 = acc  in
                     (match uu____66589 with
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
                                     (uu____66664,uu____66665,uu____66666,t_lid,uu____66668,uu____66669)
                                     -> t_lid = lid
                                 | uu____66676 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____66691 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____66691)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____66694 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____66697 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____66694, uu____66697)))
  
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
          let uu____66755 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____66765,us,uu____66767,t,uu____66769,uu____66770) ->
                (us, t)
            | uu____66779 -> failwith "Impossible!"  in
          match uu____66755 with
          | (us,t) ->
              let uu____66789 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____66789 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____66815 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____66815 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____66893 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____66893 with
                           | (uu____66908,t1) ->
                               let uu____66930 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____66930
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____66935 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____66935 with
                          | (phi1,uu____66943) ->
                              ((let uu____66945 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____66945
                                then
                                  let uu____66948 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____66948
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____66966  ->
                                         match uu____66966 with
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
                let uu____67038 =
                  let uu____67039 = FStar_Syntax_Subst.compress t  in
                  uu____67039.FStar_Syntax_Syntax.n  in
                match uu____67038 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____67047) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____67084 = is_mutual t'  in
                    if uu____67084
                    then true
                    else
                      (let uu____67091 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____67091)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____67111) ->
                    is_mutual t'
                | uu____67116 -> false
              
              and exists_mutual uu___586_67118 =
                match uu___586_67118 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____67139 =
                let uu____67140 = FStar_Syntax_Subst.compress dt1  in
                uu____67140.FStar_Syntax_Syntax.n  in
              match uu____67139 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____67146) ->
                  let dbs1 =
                    let uu____67176 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____67176  in
                  let dbs2 =
                    let uu____67226 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____67226 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____67246 =
                               let uu____67251 =
                                 let uu____67252 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____67252]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____67251
                                in
                             uu____67246 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____67282 = is_mutual sort  in
                             if uu____67282
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
                           let uu____67295 =
                             let uu____67300 =
                               let uu____67301 =
                                 let uu____67310 =
                                   let uu____67311 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____67311 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____67310  in
                               [uu____67301]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____67300
                              in
                           uu____67295 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____67358 -> acc
  
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
              let uu____67408 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____67430,bs,t,uu____67433,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____67445 -> failwith "Impossible!"  in
              match uu____67408 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____67469 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____67469 t  in
                  let uu____67478 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____67478 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____67488 =
                           let uu____67489 = FStar_Syntax_Subst.compress t2
                              in
                           uu____67489.FStar_Syntax_Syntax.n  in
                         match uu____67488 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____67493) ->
                             ibs
                         | uu____67514 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____67523 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____67524 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____67523
                           uu____67524
                          in
                       let ind1 =
                         let uu____67530 =
                           let uu____67535 =
                             FStar_List.map
                               (fun uu____67552  ->
                                  match uu____67552 with
                                  | (bv,aq) ->
                                      let uu____67571 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67571, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____67535  in
                         uu____67530 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____67577 =
                           let uu____67582 =
                             FStar_List.map
                               (fun uu____67599  ->
                                  match uu____67599 with
                                  | (bv,aq) ->
                                      let uu____67618 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67618, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____67582  in
                         uu____67577 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____67624 =
                           let uu____67629 =
                             let uu____67630 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____67630]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____67629
                            in
                         uu____67624 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____67667,uu____67668,uu____67669,t_lid,uu____67671,uu____67672)
                                  -> t_lid = lid
                              | uu____67679 -> failwith "Impossible")
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
                         let uu___1460_67691 = fml  in
                         let uu____67692 =
                           let uu____67693 =
                             let uu____67700 =
                               let uu____67701 =
                                 let uu____67714 =
                                   let uu____67725 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____67725]  in
                                 [uu____67714]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____67701
                                in
                             (fml, uu____67700)  in
                           FStar_Syntax_Syntax.Tm_meta uu____67693  in
                         {
                           FStar_Syntax_Syntax.n = uu____67692;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_67691.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_67691.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67778 =
                                  let uu____67783 =
                                    let uu____67784 =
                                      let uu____67793 =
                                        let uu____67794 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67794
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67793
                                       in
                                    [uu____67784]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67783
                                   in
                                uu____67778 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67847 =
                                  let uu____67852 =
                                    let uu____67853 =
                                      let uu____67862 =
                                        let uu____67863 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67863
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67862
                                       in
                                    [uu____67853]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67852
                                   in
                                uu____67847 FStar_Pervasives_Native.None
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
                     (lid,uu____67955,uu____67956,uu____67957,uu____67958,uu____67959)
                     -> lid
                 | uu____67968 -> failwith "Impossible!") tcs
             in
          let uu____67970 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____67982,uu____67983,uu____67984,uu____67985) ->
                (lid, us)
            | uu____67994 -> failwith "Impossible!"  in
          match uu____67970 with
          | (lid,us) ->
              let uu____68004 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____68004 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____68031 =
                       let uu____68032 =
                         let uu____68039 = get_haseq_axiom_lid lid  in
                         (uu____68039, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____68032  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____68031;
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
          let uu____68093 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_68118  ->
                    match uu___587_68118 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____68120;
                        FStar_Syntax_Syntax.sigrng = uu____68121;
                        FStar_Syntax_Syntax.sigquals = uu____68122;
                        FStar_Syntax_Syntax.sigmeta = uu____68123;
                        FStar_Syntax_Syntax.sigattrs = uu____68124;_} -> true
                    | uu____68146 -> false))
             in
          match uu____68093 with
          | (tys,datas) ->
              ((let uu____68169 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_68180  ->
                          match uu___588_68180 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____68182;
                              FStar_Syntax_Syntax.sigrng = uu____68183;
                              FStar_Syntax_Syntax.sigquals = uu____68184;
                              FStar_Syntax_Syntax.sigmeta = uu____68185;
                              FStar_Syntax_Syntax.sigattrs = uu____68186;_}
                              -> false
                          | uu____68207 -> true))
                   in
                if uu____68169
                then
                  let uu____68210 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____68210
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____68225 =
                       let uu____68226 = FStar_List.hd tys  in
                       uu____68226.FStar_Syntax_Syntax.sigel  in
                     match uu____68225 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____68229,uvs,uu____68231,uu____68232,uu____68233,uu____68234)
                         -> uvs
                     | uu____68243 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____68248 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____68278 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____68278 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____68316,bs,t,l1,l2) ->
                                      let uu____68329 =
                                        let uu____68346 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____68347 =
                                          let uu____68348 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____68348 t
                                           in
                                        (lid, univs2, uu____68346,
                                          uu____68347, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____68329
                                  | uu____68361 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_68363 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_68363.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_68363.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_68363.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_68363.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____68373,t,lid_t,x,l) ->
                                      let uu____68384 =
                                        let uu____68400 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____68400, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____68384
                                  | uu____68404 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_68406 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_68406.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_68406.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_68406.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_68406.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____68407 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____68407, tys1, datas1))
                   in
                match uu____68248 with
                | (env1,tys1,datas1) ->
                    let uu____68433 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____68472  ->
                             match uu____68472 with
                             | (env2,all_tcs,g) ->
                                 let uu____68512 = tc_tycon env2 tc  in
                                 (match uu____68512 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____68539 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____68539
                                        then
                                          let uu____68542 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____68542
                                        else ());
                                       (let uu____68547 =
                                          let uu____68548 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____68548
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____68547))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____68433 with
                     | (env2,tcs,g) ->
                         let uu____68594 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____68616  ->
                                  match uu____68616 with
                                  | (datas2,g1) ->
                                      let uu____68635 =
                                        let uu____68640 = tc_data env2 tcs
                                           in
                                        uu____68640 se  in
                                      (match uu____68635 with
                                       | (data,g') ->
                                           let uu____68657 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____68657)))
                             datas1 ([], g)
                            in
                         (match uu____68594 with
                          | (datas2,g1) ->
                              let uu____68678 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____68700 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____68700, datas2))
                                 in
                              (match uu____68678 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____68732 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____68733 =
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
                                         uu____68732;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____68733
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____68759,uu____68760)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____68780 =
                                                    let uu____68786 =
                                                      let uu____68788 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____68790 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____68788
                                                        uu____68790
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____68786)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____68780
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____68794 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____68794 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____68810)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____68841 ->
                                                             let uu____68842
                                                               =
                                                               let uu____68849
                                                                 =
                                                                 let uu____68850
                                                                   =
                                                                   let uu____68865
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____68865)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____68850
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____68849
                                                                in
                                                             uu____68842
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
                                                       let uu____68887 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____68887
                                                        with
                                                        | (uu____68892,inferred)
                                                            ->
                                                            let uu____68894 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____68894
                                                             with
                                                             | (uu____68899,expected)
                                                                 ->
                                                                 let uu____68901
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____68901
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____68908 -> ()));
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
                          let uu____69019 =
                            let uu____69026 =
                              let uu____69027 =
                                let uu____69034 =
                                  let uu____69037 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____69037
                                   in
                                (uu____69034, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____69027  in
                            FStar_Syntax_Syntax.mk uu____69026  in
                          uu____69019 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____69071  ->
                                  match uu____69071 with
                                  | (x,imp) ->
                                      let uu____69090 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____69090, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____69094 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____69094  in
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
                               let uu____69117 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____69117
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____69119 =
                               let uu____69122 =
                                 let uu____69125 =
                                   let uu____69130 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____69131 =
                                     let uu____69132 =
                                       let uu____69141 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____69141
                                        in
                                     [uu____69132]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____69130
                                     uu____69131
                                    in
                                 uu____69125 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____69122  in
                             FStar_Syntax_Util.refine x uu____69119  in
                           let uu____69166 =
                             let uu___1671_69167 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_69167.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_69167.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____69166)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____69184 =
                          FStar_List.map
                            (fun uu____69208  ->
                               match uu____69208 with
                               | (x,uu____69222) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____69184 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____69281  ->
                                match uu____69281 with
                                | (x,uu____69295) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____69306 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____69306)
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
                               (let uu____69327 =
                                  let uu____69329 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____69329.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____69327)
                              in
                           let quals =
                             let uu____69333 =
                               FStar_List.filter
                                 (fun uu___589_69337  ->
                                    match uu___589_69337 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____69342 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____69333
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____69380 =
                                 let uu____69381 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____69381  in
                               FStar_Syntax_Syntax.mk_Total uu____69380  in
                             let uu____69382 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____69382
                              in
                           let decl =
                             let uu____69386 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____69386;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____69388 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____69388
                            then
                              let uu____69392 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____69392
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
                                             fun uu____69453  ->
                                               match uu____69453 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____69478 =
                                                       let uu____69481 =
                                                         let uu____69482 =
                                                           let uu____69489 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____69489,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____69482
                                                          in
                                                       pos uu____69481  in
                                                     (uu____69478, b)
                                                   else
                                                     (let uu____69497 =
                                                        let uu____69500 =
                                                          let uu____69501 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____69501
                                                           in
                                                        pos uu____69500  in
                                                      (uu____69497, b))))
                                      in
                                   let pat_true =
                                     let uu____69520 =
                                       let uu____69523 =
                                         let uu____69524 =
                                           let uu____69538 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____69538, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____69524
                                          in
                                       pos uu____69523  in
                                     (uu____69520,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____69573 =
                                       let uu____69576 =
                                         let uu____69577 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____69577
                                          in
                                       pos uu____69576  in
                                     (uu____69573,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____69591 =
                                     let uu____69598 =
                                       let uu____69599 =
                                         let uu____69622 =
                                           let uu____69639 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____69654 =
                                             let uu____69671 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____69671]  in
                                           uu____69639 :: uu____69654  in
                                         (arg_exp, uu____69622)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____69599
                                        in
                                     FStar_Syntax_Syntax.mk uu____69598  in
                                   uu____69591 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____69747 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____69747
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
                                let uu____69769 =
                                  let uu____69774 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____69774  in
                                let uu____69775 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____69769
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____69775 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____69781 =
                                  let uu____69782 =
                                    let uu____69789 =
                                      let uu____69792 =
                                        let uu____69793 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____69793
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____69792]  in
                                    ((false, [lb]), uu____69789)  in
                                  FStar_Syntax_Syntax.Sig_let uu____69782  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____69781;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____69807 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____69807
                               then
                                 let uu____69811 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____69811
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
                                fun uu____69884  ->
                                  match uu____69884 with
                                  | (a,uu____69893) ->
                                      let uu____69898 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____69898 with
                                       | (field_name,uu____69904) ->
                                           let field_proj_tm =
                                             let uu____69906 =
                                               let uu____69907 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____69907
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____69906 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____69933 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____69975  ->
                                    match uu____69975 with
                                    | (x,uu____69986) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____69992 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____69992 with
                                         | (field_name,uu____70000) ->
                                             let t =
                                               let uu____70004 =
                                                 let uu____70005 =
                                                   let uu____70008 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____70008
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____70005
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____70004
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____70014 =
                                                    let uu____70016 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____70016.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____70014)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____70035 =
                                                   FStar_List.filter
                                                     (fun uu___590_70039  ->
                                                        match uu___590_70039
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____70042 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____70035
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_70057  ->
                                                         match uu___591_70057
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____70063 ->
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
                                               let uu____70074 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____70074;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____70076 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____70076
                                               then
                                                 let uu____70080 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____70080
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
                                                           fun uu____70134 
                                                             ->
                                                             match uu____70134
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
                                                                   let uu____70160
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____70160,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____70176
                                                                    =
                                                                    let uu____70179
                                                                    =
                                                                    let uu____70180
                                                                    =
                                                                    let uu____70187
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____70187,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____70180
                                                                     in
                                                                    pos
                                                                    uu____70179
                                                                     in
                                                                    (uu____70176,
                                                                    b))
                                                                   else
                                                                    (let uu____70195
                                                                    =
                                                                    let uu____70198
                                                                    =
                                                                    let uu____70199
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____70199
                                                                     in
                                                                    pos
                                                                    uu____70198
                                                                     in
                                                                    (uu____70195,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____70218 =
                                                     let uu____70221 =
                                                       let uu____70222 =
                                                         let uu____70236 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____70236,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____70222
                                                        in
                                                     pos uu____70221  in
                                                   let uu____70246 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____70218,
                                                     FStar_Pervasives_Native.None,
                                                     uu____70246)
                                                    in
                                                 let body =
                                                   let uu____70262 =
                                                     let uu____70269 =
                                                       let uu____70270 =
                                                         let uu____70293 =
                                                           let uu____70310 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____70310]  in
                                                         (arg_exp,
                                                           uu____70293)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____70270
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____70269
                                                      in
                                                   uu____70262
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____70375 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____70375
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
                                                   let uu____70394 =
                                                     let uu____70399 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____70399
                                                      in
                                                   let uu____70400 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____70394;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____70400;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____70406 =
                                                     let uu____70407 =
                                                       let uu____70414 =
                                                         let uu____70417 =
                                                           let uu____70418 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____70418
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____70417]  in
                                                       ((false, [lb]),
                                                         uu____70414)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____70407
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____70406;
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
                                                 (let uu____70432 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____70432
                                                  then
                                                    let uu____70436 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____70436
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____69933 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____70490) when
              let uu____70497 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____70497 ->
              let uu____70499 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____70499 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____70521 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____70521 with
                    | (formals,uu____70539) ->
                        let uu____70560 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____70595 =
                                   let uu____70597 =
                                     let uu____70598 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____70598  in
                                   FStar_Ident.lid_equals typ_lid uu____70597
                                    in
                                 if uu____70595
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____70620,uvs',tps,typ0,uu____70624,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____70644 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____70693 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____70693
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____70560 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____70731 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____70731 with
                              | (indices,uu____70749) ->
                                  let refine_domain =
                                    let uu____70772 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_70779  ->
                                              match uu___592_70779 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____70781 -> true
                                              | uu____70791 -> false))
                                       in
                                    if uu____70772
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_70806 =
                                      match uu___593_70806 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____70809,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____70821 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____70822 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____70822 with
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
                                    let uu____70835 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____70835 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____70918  ->
                                               fun uu____70919  ->
                                                 match (uu____70918,
                                                         uu____70919)
                                                 with
                                                 | ((x,uu____70945),(x',uu____70947))
                                                     ->
                                                     let uu____70968 =
                                                       let uu____70975 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____70975)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____70968) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____70980 -> []
  